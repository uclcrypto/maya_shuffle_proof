#!/bin/bash
# Single-core Verificatum benchmark.
# Forces JVM + Verificatum parallelism to 1 thread.
# Pinned to core 0 with taskset.

set -euo pipefail


export JAVA_TOOL_OPTIONS="\
-Xmx8G \
-Djava.util.concurrent.ForkJoinPool.common.parallelism=1 \
-Dcom.verificatum.eio.globalParallelism=1 \
-Dcom.verificatum.arithm.globalParallelism=1"

if [ -z "${PINNED_TO_CORE:-}" ]; then
    export PINNED_TO_CORE=1
    exec taskset -c 0 "$0" "$@"
fi


N_VALUES=(1000000 1000 10000 100000)

get_iterations() {
    local n=$1
    if   [ "$n" -le 100000 ];   then echo "50 100"
    elif [ "$n" -le 1000000 ];  then echo "50 100"
    else                             echo "50 100"
    fi
}

INTER_SLEEP=10 

MODE="singlecore"

PRIV_INFO="privInfo.xml"
PROT_INFO="protInfo.xml"
CIPH_FILE="ciphertexts"
PUB_KEY="publicKey"
ERROR_LOG="error_verificatum_${MODE}.log"
PROOF_DIR_BASE="dir/nizkp"



echo "Verificatum benchmark (single-threaded)"

calculate_mean() {
    local sum=$1 count=$2
    if [ "$count" -gt 0 ]; then
        echo "scale=3; $sum / $count" | bc -l
    else echo "N/A"; fi
}

calculate_stddev() {
    local sum_sq=$1 sum=$2 count=$3
    if [ "$count" -le 1 ]; then echo "N/A"
    else
        echo "scale=3; sqrt(($sum_sq - ($sum * $sum) / $count) / ($count - 1))" | bc -l
    fi
}

calculate_cv_percent() {
    local stddev=$1 mean=$2
    if ! [[ "$stddev" =~ ^[0-9]+(\.[0-9]+)?$ ]] || ! [[ "$mean" =~ ^[0-9]+(\.[0-9]+)?$ ]] \
       || [ "$(echo "$mean == 0" | bc -l)" -eq 1 ]; then
        echo "N/A"
    else
        echo "scale=3; ($stddev / $mean) * 100" | bc -l
    fi
}

# I. ONE-TIME SETUP 
echo "1. Performing cryptographic setup ..."
> "$ERROR_LOG" 

P256_GROUP_OBJECT=$(vog -gen ECqPGroup -name P-256 2>> "$ERROR_LOG")
if [ -z "$P256_GROUP_OBJECT" ]; then
    echo "FATAL: Failed to generate P-256 group object. See $ERROR_LOG"; exit 1
fi

vmni -prot -sid "BenchSC" -name "BenchmarkSingleCore" \
    -nopart 1 -thres 1 -rohash SHA-512 \
    -pgroup "$P256_GROUP_OBJECT" stub.xml 2>> "$ERROR_LOG"
if [ $? -ne 0 ]; then echo "FATAL: vmni -prot failed. See $ERROR_LOG"; exit 1; fi

vmni -party -name "Mix Server 1" stub.xml "$PRIV_INFO" localProtInfo.xml 2>> "$ERROR_LOG"
vmni -merge localProtInfo.xml "$PROT_INFO" 2>> "$ERROR_LOG"
vmn -keygen "$PRIV_INFO" "$PROT_INFO" "$PUB_KEY" 2>> "$ERROR_LOG"
echo "   Setup complete."
echo ""

#  II. LOOP OVER N VALUES 
for N in "${N_VALUES[@]}"; do

    read NUM_WARMUP NUM_BENCHMARK <<< $(get_iterations "$N")
    TOTAL_RUNS=$((NUM_WARMUP + NUM_BENCHMARK))
    LOG_FILE="benchmark_verificatum_${MODE}_P256_N${N}.csv"

    echo "================================================================================="
    echo " N = $N  |  warmup=$NUM_WARMUP  benchmark=$NUM_BENCHMARK  total=$TOTAL_RUNS"
    echo "================================================================================="

    # Generated once per N, outside the timed iteration loop.
    echo "   Generating $N ciphertexts..."
    vmnd -ciphs "$PUB_KEY" "$N" "$CIPH_FILE" 2>> "$ERROR_LOG"


    echo "Iteration,Type,Session_ID,Prover_Time_ms,Verifier_Time_ms,Proof_Size_bytes" > "$LOG_FILE"
    
    for i in $(seq 1 $TOTAL_RUNS); do
        if [ "$i" -le "$NUM_WARMUP" ]; then TYPE="WARMUP"; else TYPE="BENCHMARK"; fi

        AUX_SID="sc${N}r${i}"
        PLAIN_FILE="plaintexts_${N}_${i}"
        SESSION_PROOF_DIR="$PROOF_DIR_BASE/$AUX_SID"

        echo "   [$i/$TOTAL_RUNS] $TYPE  (N=$N, sid=$AUX_SID)"

        # PROVER (shuffle)
        MIX_OUTPUT=$(vmn -shuffle -auxsid "$AUX_SID" "$PRIV_INFO" "$PROT_INFO" \
                     "$CIPH_FILE" "$PLAIN_FILE" 2>&1) || true
        MIX_EXIT_CODE=${PIPESTATUS[0]:-$?}

        if [ $MIX_EXIT_CODE -ne 0 ] 2>/dev/null; then
            echo "ERROR (Shuffle) run $i N=$N. See $ERROR_LOG" >> "$ERROR_LOG"
            echo "$MIX_OUTPUT" >> "$ERROR_LOG"
            echo "$i,$TYPE,$AUX_SID,P_Failed,V_Skipped,N/A" >> "$LOG_FILE"
            vmn -delete -f -auxsid "$AUX_SID" "$PRIV_INFO" "$PROT_INFO" 2>> "$ERROR_LOG" || true
            rm -rf "$PLAIN_FILE" "$SESSION_PROOF_DIR"
            continue
        fi

        PROVER_TIME_MS=$(echo "$MIX_OUTPUT" | grep 'Effective' | tail -n 1 \
                         | awk '{print $NF}' | sed 's/[^0-9.]//g')
        [ -z "$PROVER_TIME_MS" ] && PROVER_TIME_MS="P_NA"

        # VERIFIER 
        VERIFIER_OUTPUT=$(vmnv -shuffle -v -auxsid "$AUX_SID" "$PROT_INFO" \
                          "$SESSION_PROOF_DIR" 2>&1) || true
        VERIFIER_EXIT_CODE=${PIPESTATUS[0]:-$?}

        if [ $VERIFIER_EXIT_CODE -ne 0 ] 2>/dev/null; then
            echo "ERROR (Verify) run $i N=$N" >> "$ERROR_LOG"
            echo "$VERIFIER_OUTPUT" >> "$ERROR_LOG"
            VERIFIER_TIME_MS="V_Failed"
            PROOF_SIZE_BYTES="N/A"
        else
            VERIFIER_TIME_MS=$(echo "$VERIFIER_OUTPUT" | grep 'Completed verification' \
                               | grep -oP '\([0-9]+ ms\)' | grep -oP '[0-9]+') || true
            PROOF_SIZE_BYTES=$(echo "$VERIFIER_OUTPUT" | grep 'Proof size is' \
                               | grep -oP '\([0-9]+ bytes\)' | grep -oP '[0-9]+') || true
            [ -z "$VERIFIER_TIME_MS" ]  && VERIFIER_TIME_MS="V_NA"
            [ -z "$PROOF_SIZE_BYTES" ]  && PROOF_SIZE_BYTES="N/A"
        fi


        echo "$i,$TYPE,$AUX_SID,$PROVER_TIME_MS,$VERIFIER_TIME_MS,$PROOF_SIZE_BYTES" >> "$LOG_FILE"


        vmn -delete -f -auxsid "$AUX_SID" "$PRIV_INFO" "$PROT_INFO" 2>> "$ERROR_LOG" || true
        rm -rf "$PLAIN_FILE" "$SESSION_PROOF_DIR"


        sleep "$INTER_SLEEP"
    done

    # STATISTICS 
    echo ""
    echo "   Computing statistics for N=$N ..."

    STAT_RESULTS=$(awk -F',' '
        $2 == "BENCHMARK" {
            if ($4 ~ /^[0-9]+(\.[0-9]+)?$/) {
                if (pc == 0 || $4 < pmin) pmin = $4;
                if (pc == 0 || $4 > pmax) pmax = $4;
                psum += $4; pssq += $4*$4; pc++;
            }
            if ($5 ~ /^[0-9]+(\.[0-9]+)?$/) {
                if (vc == 0 || $5 < vmin) vmin = $5;
                if (vc == 0 || $5 > vmax) vmax = $5;
                vsum += $5; vssq += $5*$5; vc++;
            }
        }
        END {
            printf "%.3f %.3f %d %.3f %.3f\n", psum, pssq, pc, pmin, pmax;
            printf "%.3f %.3f %d %.3f %.3f\n", vsum, vssq, vc, vmin, vmax;
        }
    ' "$LOG_FILE")

    read PSUM PSSQ PC PMIN PMAX <<< $(echo "$STAT_RESULTS" | head -1)
    read VSUM VSSQ VC VMIN VMAX <<< $(echo "$STAT_RESULTS" | tail -1)

    PMEAN=$(calculate_mean "$PSUM" "$PC")
    PSD=$(calculate_stddev "$PSSQ" "$PSUM" "$PC")
    PCV=$(calculate_cv_percent "$PSD" "$PMEAN")
    VMEAN=$(calculate_mean "$VSUM" "$VC")
    VSD=$(calculate_stddev "$VSSQ" "$VSUM" "$VC")
    VCV=$(calculate_cv_percent "$VSD" "$VMEAN")

    {
        echo ""
        echo "--- Summary N=$N  Mode=$MODE  (Prover: $PC runs, Verifier: $VC runs) ---"
        echo "Statistic,Prover_Time_ms,Verifier_Time_ms"
        echo "Mean,$PMEAN,$VMEAN"
        echo "StdDev,$PSD,$VSD"
        echo "CV%,$PCV,$VCV"
        echo "Min,$PMIN,$VMIN"
        echo "Max,$PMAX,$VMAX"
    } >> "$LOG_FILE"

    echo "     N=$N done. Results in $LOG_FILE"
    echo "     Prover mean: ${PMEAN} ms   Verifier mean: ${VMEAN} ms"
    echo ""
done

