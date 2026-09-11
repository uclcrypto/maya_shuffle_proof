# MAYA: A Short Shuffle Argument With Fast Verification

This repository contains a Rust implementation of the MAYA shuffle argument with
O(log n) communication complexity. Two curve instantiations are provided: one based on
curve25519-dalek (Ristretto255) and one based on the arkworks library (NIST P-256).
This repository accompanies the MAYA paper accepted at CCS ’26.

More information about MAYA, including a verifier-oriented specification, is available on the https://thaodoanvan.github.io/maya_website/.


## Requirements

- **Hardware**: x86-64 CPU, minimum 8 GB RAM (16 GB is recommended)
- **Software**: Rust >= 1.81 (install via [rustup](https://rustup.rs))

## Repository Structure

```
maya_ristretto/       # Primary instantiation (Ristretto255, curve25519-dalek)
  src/                # Library source
  benches/r1cs.rs     # Benchmark: prover and verifier timing
  Cargo.toml
maya_p256/            # Secondary instantiation (NIST P-256, arkworks)
  src/                # Library source
  benches/r1cs.rs     # Benchmark: prover and verifier timing
  Cargo.toml
Verificatum_singlecore.sh   # Baseline: Verificatum single-threaded
Verificatum_multicore.sh    # Baseline: Verificatum multi-threaded
README.md
```

## Quick Start

```bash
cd maya_ristretto
cargo build --release --features yoloproofs,parallel
QUICK=1 RUSTFLAGS='-C target_cpu=native' cargo bench --bench r1cs --features yoloproofs,parallel
```

**Notes**

- First benchmark run may take some minutes due to dependency compilation.
- Benchmark timings are more stable after the initial build.
- For stable numbers, run while plugged in and avoid background load.

## Reproducing Paper Results


### Tables 1 and 2 - Prover and Verifier Performance

Single-threaded:
```bash
cd maya_ristretto
RUSTFLAGS='-C target_cpu=native' cargo bench --bench r1cs --features yoloproofs
```

Multi-threaded:
```bash
cd maya_ristretto
RUSTFLAGS='-C target_cpu=native' cargo bench --bench r1cs --features yoloproofs,parallel
```

For each of the 8 configurations (N in {10^3, 10^4, 10^5, 10^6}, k in {2, 4}), the output
shows a per-phase breakdown followed by totals. A summary table is printed at the end.

### Figure 3 - Sweet Spot Analysis

```bash
cd maya_ristretto
BENCH_FOLDING=1 RUSTFLAGS='-C target_cpu=native' cargo bench --bench r1cs --features yoloproofs
```

Runs proof generation across k in {2, 3, 4, 5, 6, 8, 16} for N in {10^3,...,10^6}.
A table of normalized times (relative to k=2) is printed at the end.


### Tables 8-11 - MAYA-P256 (Appendices O, P)

```bash
cd maya_p256
RUSTFLAGS='-C target_cpu=native' cargo bench --bench r1cs --features yoloproofs,asm          # single-threaded
RUSTFLAGS='-C target_cpu=native' cargo bench --bench r1cs --features yoloproofs,parallel,asm  # multi-threaded
```

### Table 12 - Padding Comparison (Appendix R)

Iterative padding (default):
```bash
cd maya_ristretto
BENCH_PADDING=1 RUSTFLAGS='-C target_cpu=native' cargo bench --bench r1cs --features yoloproofs
```

Global padding:
```bash
cd maya_ristretto
BENCH_PADDING=1 RUSTFLAGS='-C target_cpu=native' cargo bench --bench r1cs --features yoloproofs,global_padding
```

### Multi-run averaging

An alternative averaging benchmark measures the complete prover and verifier pipelines over multiple runs, reporting the mean and standard deviation for each configuration.

The benchmarks used for Tables 1-2 above rely on Criterion's built-in averaging. Both approaches produce similar results. Criterion provides a more detailed per-phase timing breakdown, while  the multi-run averaging benchmark reports a single end-to-end runtime.

```bash
cd maya_ristretto
BENCH_FULL_AVG=1 RUSTFLAGS='-C target_cpu=native' cargo bench --bench r1cs --features yoloproofs
BENCH_FULL_AVG=1 RUSTFLAGS='-C target_cpu=native' cargo bench --bench r1cs --features yoloproofs,parallel
```

```bash
cd maya_p256
BENCH_FULL_AVG=1 RUSTFLAGS='-C target_cpu=native' cargo bench --bench r1cs --features yoloproofs,asm
BENCH_FULL_AVG=1 RUSTFLAGS='-C target_cpu=native' cargo bench --bench r1cs --features yoloproofs,parallel,asm
```

Default is 10 runs/config to keep runtime manageable. Override with NUM_RUNS=100.

### Verificatum Baseline (Tables 1-2, Verificatum column)

Requires Verificatum v3.1.0 and Java 17+. See https://www.verificatum.org/.
```bash
./Verificatum_singlecore.sh
./Verificatum_multicore.sh
```

## Result Mapping

| Paper Results | Section | Command |
| --- | --- | --- |
| Prover (Single-Threaded) | Table 1 | `cargo bench --bench r1cs --features yoloproofs` |
| Prover (Multi-Threaded) | Table 1 | `cargo bench --bench r1cs --features yoloproofs,parallel` |
| Verifier (Single-Threaded) | Table 2 | Same as Table 1 (Single-Threaded) |
| Verifier (Multi-Threaded) | Table 2 | Same as Table 1 (Multi-Threaded) |
| Proof size | Section 4.3.3 | Any run with `N=10^6`, `k=4` |
| Sweet spot | Figure 3 | `BENCH_FOLDING=1 cargo bench ...` |
| Padding strategies | Table 12 | `BENCH_PADDING=1 cargo bench ...` |
| MAYA-P256 | Tables 8–11 | `cd maya_p256 && cargo bench ...` |
| Verificatum baseline | Tables 1–2 | `./Verificatum_singlecore.sh` or `./Verificatum_multicore.sh` |
| Full averaging | Tables 1–2 | `BENCH_FULL_AVG=1 cargo bench ...` |
## Interpreting Results

The numbers in the paper were measured on an Intel Core i5-1245U (12 threads, 4.4 GHz), 16 GB RAM,
Ubuntu 22.04, rustc 1.88.0.
