// MAYA-P256 Benchmark - P-256 / secp256r1

use maya_p256::fixed_base::FixedBaseTable;
use maya_p256::r1cs::LinearCombination;
use maya_p256::r1cs::{ConstraintSystem, Prover, R1CSError, R1CSProof, Variable, Verifier};
use maya_p256::transcript::{point_to_bytes, TranscriptProtocol};
use maya_p256::{BulletproofGens, PedersenGens};

use ark_ec::{CurveGroup, VariableBaseMSM};
use ark_ff::{One, UniformRand, Zero};
use ark_secp256r1::Fr;
use ark_secp256r1::Projective as G;

use criterion::{criterion_group, criterion_main, Criterion};
use merlin::Transcript;
use rand::seq::SliceRandom;
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use std::time::Instant;

use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, Validate};
use std::fs::File;
use std::io::{BufReader, BufWriter, Read, Write};

#[cfg(feature = "parallel")]
use rayon::prelude::*;


#[allow(dead_code)]
const N: usize = 1000;
#[allow(dead_code)]
const K: usize = 2;
#[allow(dead_code)]
const D: usize = 20;

/// Number of benchmark samples
const SAMPLES: usize = 10;

const CRITERION_ENABLED: bool = true;

// --- Padding helpers---

const fn pow_usize(base: usize, exp: usize) -> usize {
    let mut result = 1;
    let mut i = 0;
    while i < exp {
        result *= base;
        i += 1;
    }
    result
}

#[allow(dead_code)]
const fn compute_m(n: usize, k_pow_d: usize) -> usize {
    (n + k_pow_d - 1) / k_pow_d
}

#[allow(dead_code)]
const K_POW_D: usize = pow_usize(K, D);
#[allow(dead_code)]
const M: usize = compute_m(N, K_POW_D);
#[allow(dead_code)]
const N_PADDED: usize = M * K_POW_D;
#[allow(dead_code)]
const PADDING: usize = N_PADDED - N;

// ---  Shuffle Gadget ---
struct KShuffleGadget;

impl KShuffleGadget {
    fn fill_cs<CS: ConstraintSystem<G, ScalarField = Fr>>(
        cs: &mut CS,
        x: &[Variable],
        y: &[Fr],
        k_original: usize,
    ) {
        let z: Fr = cs.challenge_scalar(b"k-scalar shuffle challenge");
        let k = x.len();
        assert_eq!(x.len(), y.len());

        let mut prod_y = Fr::one();
        for yi in y {
            prod_y *= *yi - z;
        }

        let mut prev_lc: LinearCombination<Fr> = if k_original == 0 {
            cs.constrain(LinearCombination::from(x[0]) - LinearCombination::from(Fr::zero()));
            LinearCombination::from(-z)
        } else {
            LinearCombination::from(x[0]) - LinearCombination::from(z)
        };

        for i in 1..k {
            if i >= k_original {
                cs.constrain(LinearCombination::from(x[i]) - LinearCombination::from(Fr::zero()));
                prev_lc = prev_lc * (-z);
            } else {
                let term: LinearCombination<Fr> =
                    LinearCombination::from(x[i]) - LinearCombination::from(z);
                let (_, _, out_var) = cs.multiply(prev_lc, term);
                prev_lc = LinearCombination::from(out_var);
            }
        }
        cs.constrain(prev_lc - LinearCombination::from(prod_y));
    }

    pub fn prove(
        pc_gens: &PedersenGens<G>,
        bp_gens: &BulletproofGens<G>,
        transcript: &mut Transcript,
        input: &[Fr],
        output: &[Fr],
        c1_prime: &[G],
        c2_prime: &[G],
        r_prime: Fr,
        k_fold: usize,
        num_rounds: usize,
        rng: &mut impl rand::RngCore,
    ) -> Result<(R1CSProof<G>, Vec<u8>), R1CSError> {
        let k = input.len();
        let k_original = c1_prime.len();
        if k <= 1 {
            return Err(R1CSError::InputLengthError);
        }

        let mut scalar_buf = Vec::new();
        ark_serialize::CanonicalSerialize::serialize_compressed(
            &Fr::from(k as u64),
            &mut scalar_buf,
        )
        .unwrap();
        transcript.append_message(b"dom-sep", b"ShuffleProof");
        transcript.append_message(b"k", &scalar_buf);

        let mut prover = Prover::<G>::new(bp_gens, pc_gens, transcript);
        let v_blinding = Fr::rand(rng);
        let (output_commitment, output_vars) = prover.commit_vec(output, v_blinding, k_original);
        let mut cs = prover.finalize_inputs();
        Self::fill_cs(&mut cs, &output_vars, input, k_original);
        let proof = cs.prove(c1_prime, c2_prime, r_prime, k_fold, num_rounds)?;
        Ok((proof, output_commitment))
    }

    pub fn verify(
        pc_gens: &PedersenGens<G>,
        bp_gens: &BulletproofGens<G>,
        transcript: &mut Transcript,
        proof: &R1CSProof<G>,
        input: &[Fr],
        output_commitment: Vec<u8>,
        c1_prime: &[G],
        c2_prime: &[G],
        c_combined: &[G],
    ) -> Result<(), R1CSError> {
        let k = input.len();
        let mut scalar_buf = Vec::new();
        ark_serialize::CanonicalSerialize::serialize_compressed(
            &Fr::from(k as u64),
            &mut scalar_buf,
        )
        .unwrap();
        transcript.append_message(b"dom-sep", b"ShuffleProof");
        transcript.append_message(b"k", &scalar_buf);

        let mut verifier = Verifier::<G>::new(bp_gens, pc_gens, transcript);
        let output_vars = verifier.commit_vec(output_commitment, k);
        let mut cs = verifier.finalize_inputs();
        let k_original = c1_prime.len();
        Self::fill_cs(&mut cs, &output_vars, input, k_original);
        cs.verify(proof, c1_prime, c2_prime, c_combined)
    }
}


// Derive the challenge vector e deterministically from public parameters via
// Fiat-Shamir: e = PRG(Hash(pk, ck, C, C'))
 
fn derive_challenge_e(
    pc_gens: &PedersenGens<G>,
    bp_gens: &BulletproofGens<G>,
    c1_bytes: &[u8],
    c2_bytes: &[u8],
    c1p_bytes: &[u8],
    c2p_bytes: &[u8],
    n_original: usize,
    n_padded: usize,
) -> Vec<Fr> {
    let verbose = std::env::var("VERBOSE").ok()
        .filter(|v| v == "1" || v.eq_ignore_ascii_case("true"))
        .is_some();
    let mut ts = Transcript::new(b"FiatShamir-e");
    ts.append_message(b"dom-sep", b"challenge-e-derivation");

    <Transcript as TranscriptProtocol<G>>::commit_point(
        &mut ts,
        b"pk_g",
        &point_to_bytes(&pc_gens.B),
    );
    <Transcript as TranscriptProtocol<G>>::commit_point(
        &mut ts,
        b"pk_f",
        &point_to_bytes(&pc_gens.F),
    );
    <Transcript as TranscriptProtocol<G>>::commit_point(
        &mut ts,
        b"ck_h",
        &point_to_bytes(&pc_gens.B_blinding),
    );

    <Transcript as TranscriptProtocol<G>>::commit_u64(
        &mut ts,
        b"ck_n",
        bp_gens.gens_capacity as u64,
    );
    if let Some(g0) = bp_gens.G_vec.get(0).and_then(|v| v.get(0)) {
        <Transcript as TranscriptProtocol<G>>::commit_point(&mut ts, b"ck_g0", &point_to_bytes(g0));
    }
    if let Some(h0) = bp_gens.H_vec.get(0).and_then(|v| v.get(0)) {
        <Transcript as TranscriptProtocol<G>>::commit_point(&mut ts, b"ck_h0", &point_to_bytes(h0));
    }

    let t_transcript = Instant::now();
    for chunk in c1_bytes.chunks(33) {
        ts.append_message(b"c1", chunk);
    }
    for chunk in c2_bytes.chunks(33) {
        ts.append_message(b"c2", chunk);
    }
    for chunk in c1p_bytes.chunks(33) {
        ts.append_message(b"c1p", chunk);
    }
    for chunk in c2p_bytes.chunks(33) {
        ts.append_message(b"c2p", chunk);
    }
    if verbose {
        eprintln!(
            "[derive_e] n={}: transcript feed 4N bytes: {:?}",
            n_original,
            t_transcript.elapsed()
        );
    }

    let t_expand = Instant::now();
    let mut seed = [0u8; 32];
    ts.challenge_bytes(b"e_seed", &mut seed);
    let mut prg = ChaCha20Rng::from_seed(seed);

    let mut e: Vec<Fr> = (0..n_original).map(|_| Fr::rand(&mut prg)).collect();
    e.resize(n_padded, Fr::zero());
    if verbose {
        eprintln!(
            "[derive_e] n={}: seed-squeeze + scalar expand: {:?}",
            n_original,
            t_expand.elapsed()
        );
    }

    e
}

// Benchmark-only deterministic RNG.
// Replace with OsRng or another OS-seeded CSPRNG outside tests/benchmarks.
#[cfg(all(feature = "parallel", not(feature = "production")))]
fn deterministic_rand_fr(index: usize) -> Fr {
    use ark_ff::UniformRand;
    use rand::SeedableRng;
    let mut seed = [0u8; 32];
    seed[..8].copy_from_slice(&(index as u64).to_le_bytes());
    seed[8..16].copy_from_slice(&0xCAFEu64.to_le_bytes()); 
    let mut thread_rng = rand::rngs::StdRng::from_seed(seed);
    Fr::rand(&mut thread_rng)
}

// --- File I/O Helpers ---
fn write_ciphertexts(
    path: &str,
    c1: &[G],
    c2: &[G],
    g: &G,
    f: &G,
    h: &G,
) -> std::io::Result<usize> {
    let n = c1.len();
    assert_eq!(n, c2.len());
    let file = File::create(path)?;
    let mut w = BufWriter::new(file);
    w.write_all(&(n as u64).to_le_bytes())?;

    #[cfg(feature = "parallel")]
    {
        let (c1_blob, c2_blob) = rayon::join(
            || batch_serialize_compressed(c1),
            || batch_serialize_compressed(c2),
        );
        w.write_all(&c1_blob)?;
        w.write_all(&c2_blob)?;
    }
    #[cfg(not(feature = "parallel"))]
    for pt in c1.iter().chain(c2.iter()) {
        pt.serialize_with_mode(&mut w, Compress::Yes)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, format!("{e}")))?;
    }

    g.serialize_with_mode(&mut w, Compress::Yes)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, format!("{e}")))?;
    f.serialize_with_mode(&mut w, Compress::Yes)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, format!("{e}")))?;
    h.serialize_with_mode(&mut w, Compress::Yes)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, format!("{e}")))?;

    w.flush()?;
    let fh = w.into_inner()?;
    fh.sync_all()?;
    Ok(std::fs::metadata(path)?.len() as usize)
}

fn read_ciphertexts(path: &str) -> std::io::Result<(Vec<G>, Vec<G>, G, G, G, Vec<u8>, Vec<u8>)> {
    let file = File::open(path)?;
    let mut r = BufReader::new(file);
    let mut buf = [0u8; 8];
    r.read_exact(&mut buf)?;
    let n = u64::from_le_bytes(buf) as usize;

    #[cfg(feature = "parallel")]
    let (c1, c2, c1_raw, c2_raw) = {
        let mut blob = vec![0u8; 2 * n * 33];
        r.read_exact(&mut blob)?;
        let mid = n * 33;
        let c1_raw = blob[..mid].to_vec();
        let c2_raw = blob[mid..].to_vec();
        let (c1_blob, c2_blob) = blob.split_at(mid);
        let (c1r, c2r) = rayon::join(
            || batch_deserialize_compressed(c1_blob),
            || batch_deserialize_compressed(c2_blob),
        );
        (c1r?, c2r?, c1_raw, c2_raw)
    };
    #[cfg(not(feature = "parallel"))]
    let (c1, c2, c1_raw, c2_raw) = {
        let mut c1 = Vec::with_capacity(n);
        let mut c2 = Vec::with_capacity(n);
        let mut c1_raw = Vec::with_capacity(n * 33);
        let mut c2_raw = Vec::with_capacity(n * 33);
        let mut buf33 = [0u8; 33];
        for _ in 0..n {
            r.read_exact(&mut buf33)?;
            c1_raw.extend_from_slice(&buf33);
            c1.push(
                G::deserialize_with_mode(buf33.as_slice(), Compress::Yes, Validate::No)
                    .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, format!("{e}")))?,
            );
        }
        for _ in 0..n {
            r.read_exact(&mut buf33)?;
            c2_raw.extend_from_slice(&buf33);
            c2.push(
                G::deserialize_with_mode(buf33.as_slice(), Compress::Yes, Validate::No)
                    .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, format!("{e}")))?,
            );
        }
        (c1, c2, c1_raw, c2_raw)
    };

    let g = G::deserialize_with_mode(&mut r, Compress::Yes, Validate::No).map_err(|e| {
        std::io::Error::new(std::io::ErrorKind::Other, format!("decompress g: {e}"))
    })?;
    let f = G::deserialize_with_mode(&mut r, Compress::Yes, Validate::No).map_err(|e| {
        std::io::Error::new(std::io::ErrorKind::Other, format!("decompress f: {e}"))
    })?;
    let h = G::deserialize_with_mode(&mut r, Compress::Yes, Validate::No).map_err(|e| {
        std::io::Error::new(std::io::ErrorKind::Other, format!("decompress h: {e}"))
    })?;

    Ok((c1, c2, g, f, h, c1_raw, c2_raw))
}

#[allow(dead_code)]
fn write_scalars(path: &str, scalars: &[Fr]) -> std::io::Result<()> {
    let file = File::create(path)?;
    let mut w = BufWriter::new(file);
    w.write_all(&(scalars.len() as u64).to_le_bytes())?;
    for s in scalars {
        s.serialize_with_mode(&mut w, Compress::Yes)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, format!("{e}")))?;
    }
    w.flush()?;
    let f = w.into_inner()?;
    f.sync_all()?;
    Ok(())
}

#[allow(dead_code)]
fn read_scalars(path: &str) -> std::io::Result<Vec<Fr>> {
    let file = File::open(path)?;
    let mut r = BufReader::new(file);
    let mut buf = [0u8; 8];
    r.read_exact(&mut buf)?;
    let n = u64::from_le_bytes(buf) as usize;
    let mut out = Vec::with_capacity(n);
    for _ in 0..n {
        out.push(
            Fr::deserialize_with_mode(&mut r, Compress::Yes, Validate::No)
                .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, format!("{e}")))?,
        );
    }
    Ok(out)
}

fn batch_serialize_compressed(points: &[G]) -> Vec<u8> {
    if points.is_empty() {
        return Vec::new();
    }
    #[cfg(feature = "parallel")]
    {
        let affines = G::normalize_batch(points);
        let mut blob = vec![0u8; affines.len() * 33];
        affines
            .par_iter()
            .zip(blob.par_chunks_mut(33))
            .for_each(|(pt, chunk)| {
                pt.serialize_with_mode(chunk, Compress::Yes)
                    .expect("batch_serialize_compressed: serialize_with_mode");
            });
        return blob;
    }
    #[allow(unreachable_code)]
    {
        let mut blob = Vec::with_capacity(points.len() * 33);
        for pt in points {
            pt.serialize_with_mode(&mut blob, Compress::Yes)
                .expect("batch_serialize_compressed: serialize_with_mode");
        }
        blob
    }
}

fn batch_deserialize_compressed(blob: &[u8]) -> std::io::Result<Vec<G>> {
    if blob.is_empty() {
        return Ok(Vec::new());
    }
    assert_eq!(
        blob.len() % 33,
        0,
        "blob length must be a multiple of 33 bytes"
    );
    #[cfg(feature = "parallel")]
    {
        blob.par_chunks(33)
            .map(|chunk| {
                G::deserialize_with_mode(chunk, Compress::Yes, Validate::No)
                    .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, format!("{e}")))
            })
            .collect()
    }
    #[cfg(not(feature = "parallel"))]
    {
        let mut out = Vec::with_capacity(blob.len() / 33);
        for chunk in blob.chunks(33) {
            out.push(
                G::deserialize_with_mode(chunk, Compress::Yes, Validate::No)
                    .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, format!("{e}")))?,
            );
        }
        Ok(out)
    }
}

fn write_proof_bundle(
    path: &str,
    proof: &R1CSProof<G>,
    out_commitment: &[u8],
    c1p_blob: &[u8],
    c2p_blob: &[u8],
) -> std::io::Result<usize> {
    let file = File::create(path)?;
    let mut w = BufWriter::new(file);

    let proof_bytes = bincode::serialize(proof).expect("proof bincode serialize");

    w.write_all(&(proof_bytes.len() as u64).to_le_bytes())?;
    w.write_all(&proof_bytes)?;

    w.write_all(&(out_commitment.len() as u64).to_le_bytes())?;
    w.write_all(out_commitment)?;

    let n1 = c1p_blob.len() / 33;
    let n2 = c2p_blob.len() / 33;
    w.write_all(&(n1 as u64).to_le_bytes())?;
    w.write_all(c1p_blob)?;
    w.write_all(&(n2 as u64).to_le_bytes())?;
    w.write_all(c2p_blob)?;

    w.flush()?;
    let fh = w.into_inner()?;
    fh.sync_all()?;
    Ok(std::fs::metadata(path)?.len() as usize)
}

fn read_proof_bundle(
    path: &str,
) -> std::io::Result<(R1CSProof<G>, Vec<u8>, Vec<G>, Vec<G>, Vec<u8>, Vec<u8>)> {
    let file = File::open(path)?;
    let mut r = BufReader::new(file);
    let mut buf8 = [0u8; 8];

    r.read_exact(&mut buf8)?;
    let proof_len = u64::from_le_bytes(buf8) as usize;
    let mut proof_bytes = vec![0u8; proof_len];
    r.read_exact(&mut proof_bytes)?;
    let proof: R1CSProof<G> =
        bincode::deserialize(&proof_bytes).expect("proof bincode deserialize");

    r.read_exact(&mut buf8)?;
    let oc_len = u64::from_le_bytes(buf8) as usize;
    let mut out_commitment = vec![0u8; oc_len];
    r.read_exact(&mut out_commitment)?;

    r.read_exact(&mut buf8)?;
    let n1 = u64::from_le_bytes(buf8) as usize;
    let mut c1p_blob = vec![0u8; n1 * 33];
    r.read_exact(&mut c1p_blob)?;

    r.read_exact(&mut buf8)?;
    let n2 = u64::from_le_bytes(buf8) as usize;
    let mut c2p_blob = vec![0u8; n2 * 33];
    r.read_exact(&mut c2p_blob)?;

    #[cfg(feature = "parallel")]
    let (c1_prime, c2_prime) = {
        let (r1, r2) = rayon::join(
            || batch_deserialize_compressed(&c1p_blob),
            || batch_deserialize_compressed(&c2p_blob),
        );
        (r1?, r2?)
    };
    #[cfg(not(feature = "parallel"))]
    let c1_prime = batch_deserialize_compressed(&c1p_blob)?;
    #[cfg(not(feature = "parallel"))]
    let c2_prime = batch_deserialize_compressed(&c2p_blob)?;

    Ok((
        proof,
        out_commitment,
        c1_prime,
        c2_prime,
        c1p_blob,
        c2p_blob,
    ))
}

// --- Tables 8-11 (Appendices O, P)---
fn custom_benchmark(c: &mut Criterion) {
    if std::env::var("BENCH_FULL_AVG").is_ok() {
        return;
    }
    let quick_mode = std::env::var("QUICK")
        .ok()
        .filter(|v| v == "1" || v.eq_ignore_ascii_case("true"))
        .is_some();

    let configs: &[(usize, usize)] = if quick_mode {
        &[(1_000, 4)]
    } else {
        &[
            (1_000, 2), (1_000, 4),
            (10_000, 2), (10_000, 4),
            (100_000, 2), (100_000, 4),
            (1_000_000, 2), (1_000_000, 4),
        ]
    };

    let features = {
        let mut fv = Vec::new();
        if cfg!(feature = "parallel") {
            fv.push("parallel");
        }
        if cfg!(feature = "asm") {
            fv.push("asm");
        }
        if fv.is_empty() {
            fv.push("none");
        }
        fv.join(", ")
    };

    println!();
    println!("================================================================");
    if quick_mode {
        println!("  MAYA-P256 (NIST P-256 / arkworks)");
        println!("  Running a single config (N=1000, k=4) to verify the benchmark");
        println!("  wires up correctly. For full results, run without QUICK=1.");
        println!("  ----------------------------------------------------------------");
    }
    println!("  Configurations ({} total):", configs.len());
    for (idx, &(n, k)) in configs.iter().enumerate() {
        println!("    {:>2}.  N = {:>9}   k = {}", idx + 1, n, k);
    }
    println!();
    println!("  Features: {}", features);
    println!("================================================================");

    let input_ciph_path = "./maya_p256_bench_input_ciph.bin";
    let output_bundle_path = "./maya_p256_bench_output_bundle.bin";

    struct RunResult {
        n: usize,
        k: usize,
        d: usize,
        total_prover_ms: f64,
        total_verifier_ms: f64,
        proof_bytes: usize,
        proof_gen_ms: f64,
        verify_ms: f64,
    }
    let mut results: Vec<RunResult> = Vec::new();

    for (i, &(n_input, k)) in configs.iter().enumerate() {
        let n_padded_upper = n_input + (k - 1) + 1; // safety margin

        let t_gen_start = Instant::now();

        #[cfg(feature = "parallel")]
        let (pc_gens, bp_gens) = rayon::join(
            || PedersenGens::<G>::default(),
            || BulletproofGens::<G>::new(n_padded_upper, 1),
        );
        #[cfg(not(feature = "parallel"))]
        let pc_gens = PedersenGens::<G>::default();
        #[cfg(not(feature = "parallel"))]
        let bp_gens = BulletproofGens::<G>::new(n_padded_upper, 1);

        let t_gen = t_gen_start.elapsed();

        let mut rng = rand::thread_rng();

        let g = pc_gens.B;
        let f = pc_gens.F;

        let t_table_start = Instant::now();
        let g_table = FixedBaseTable::create(&g, 5);
        let f_table = FixedBaseTable::create(&f, 5);
        let t_table = t_table_start.elapsed();
        let _table_size_bytes = g_table.table_size_bytes();

        let rem = n_input % k;
        let circuit_n = if rem == 0 {
            n_input
        } else {
            n_input + (k - rem)
        };

        let mut n_j = circuit_n;
        let mut d = 0usize;
        while n_j > 1 {
            let r = n_j % k;
            let p = if r == 0 { 0 } else { k - r };
            n_j = (n_j + p) / k;
            d += 1;
        }
        let _m_final = n_j; 

        let mut total_pad = 0usize;
        let mut nj2 = n_input;
        for _ in 0..d {
            let r = nj2 % k;
            let p = if r == 0 { 0 } else { k - r };
            total_pad += p;
            nj2 = (nj2 + p) / k;
        }
        let _padding_pct = total_pad as f64 / n_input as f64 * 100.0;

        let c1_raw: Vec<G> = (0..n_input).map(|_| G::rand(&mut rng)).collect();
        let c2_raw: Vec<G> = (0..n_input).map(|_| G::rand(&mut rng)).collect();

        let _input_file_size = write_ciphertexts(
            input_ciph_path,
            &c1_raw,
            &c2_raw,
            &g,
            &f,
            &pc_gens.B_blinding,
        )
        .expect("write_ciphertexts failed");

        // SINGLE-RUN PROVER 

        // [1] Read ciphertexts + g + f + h 
        let t_file_read_start = Instant::now();
        let (c1, c2, g_read, f_read, _h_read, c1_bytes, c2_bytes) =
            read_ciphertexts(input_ciph_path).expect("read_ciphertexts failed");
        let t_file_read = t_file_read_start.elapsed();

        let _ = (g_read, f_read); 

        // [2] Permutation
        let t_shuffle_start = Instant::now();
        let mut indices: Vec<usize> = (0..n_input).collect();
        indices.shuffle(&mut rng);
        let c1_prime_init: Vec<G> = indices.iter().map(|&i| c1[i]).collect();
        let c2_prime_init: Vec<G> = indices.iter().map(|&i| c2[i]).collect();
        let t_shuffle = t_shuffle_start.elapsed();

        // [3] Rerandomization + Fiat-Shamir e
        let t_rerand_start = Instant::now();

        #[cfg(all(feature = "parallel", not(feature = "production")))]
        let r_values: Vec<Fr> = (0..n_input).map(|j| deterministic_rand_fr(j)).collect();
        #[cfg(not(feature = "parallel"))]
        let r_values: Vec<Fr> = (0..n_input).map(|_| Fr::rand(&mut rng)).collect();

        #[cfg(feature = "parallel")]
        let (c1_prime, c2_prime) = {
            let mut c1p = c1_prime_init;
            let mut c2p = c2_prime_init;
            c1p.par_iter_mut()
                .zip(c2p.par_iter_mut())
                .zip(r_values.par_iter())
                .for_each(|((a, b), r)| {
                    *a += g_table.mul(r);
                    *b += f_table.mul(r);
                });
            (c1p, c2p)
        };
        #[cfg(not(feature = "parallel"))]
        let (c1_prime, c2_prime) = {
            let mut c1p = c1_prime_init;
            let mut c2p = c2_prime_init;
            for (j, r) in r_values.iter().enumerate() {
                c1p[j] += g_table.mul(r);
                c2p[j] += f_table.mul(r);
            }
            (c1p, c2p)
        };

        let t_rerand = t_rerand_start.elapsed();

        let t_e_prover_start = Instant::now();
        let c1p_bytes = batch_serialize_compressed(&c1_prime);
        let c2p_bytes = batch_serialize_compressed(&c2_prime);
        let input_padded = derive_challenge_e(
            &pc_gens, &bp_gens, &c1_bytes, &c2_bytes, &c1p_bytes, &c2p_bytes, n_input, circuit_n,
        );
        let mut output_padded: Vec<Fr> = indices.iter().map(|&i| input_padded[i]).collect();
        output_padded.resize(circuit_n, Fr::zero());
        let r_prime: Fr = -(0..n_input)
            .map(|j| r_values[j] * input_padded[indices[j]])
            .sum::<Fr>();
        let t_e_prover = t_e_prover_start.elapsed();

        // [4] Proof generation
        let t_proof_start = Instant::now();
        let mut prover_transcript = Transcript::new(b"MAYA-Shuffle-v1");
        let (proof, out_commitment) = KShuffleGadget::prove(
            &pc_gens,
            &bp_gens,
            &mut prover_transcript,
            &input_padded,
            &output_padded,
            &c1_prime,
            &c2_prime,
            r_prime,
            k,
            d,
            &mut rng,
        )
        .expect("Proof generation failed");
        let t_proof_gen = t_proof_start.elapsed();

        // [5] Write proof bundle
        let t_write_start = Instant::now();
        let _output_file_size = write_proof_bundle(
            output_bundle_path,
            &proof,
            &out_commitment,
            &c1p_bytes,
            &c2p_bytes,
        )
        .expect("write_proof_bundle failed");
        let t_file_write = t_write_start.elapsed();

        let proof_size = proof.to_bytes().len();

        // SINGLE-RUN VERIFIER 

        // [0] Verifier regenerates CRS 
        let t_v_gen_start = Instant::now();
        let v_pc_gens = PedersenGens::<G>::default();
        let v_bp_gens = BulletproofGens::<G>::new(n_padded_upper, 1);
        let t_v_gen = t_v_gen_start.elapsed();

        // [1] Read proof bundle + ciphertexts (+ g, f, h)
        let t_v_read_start = Instant::now();
        let (proof_r, out_commitment_r, c1_prime_r, c2_prime_r, c1p_r_bytes, c2p_r_bytes) =
            read_proof_bundle(output_bundle_path).expect("read_proof_bundle failed");
        let (c1_orig, c2_orig, _g_v, _f_v, _h_v, c1_orig_bytes, c2_orig_bytes) =
            read_ciphertexts(input_ciph_path).expect("verifier read_ciphertexts failed");
        let t_v_file_read = t_v_read_start.elapsed();

        // [2] Derive e
        let t_e_start = Instant::now();
        let input_padded_r = derive_challenge_e(
            &v_pc_gens,
            &v_bp_gens,
            &c1_orig_bytes,
            &c2_orig_bytes,
            &c1p_r_bytes,
            &c2p_r_bytes,
            n_input,
            circuit_n,
        );
        let t_e_derive = t_e_start.elapsed();

        // [3] RHS MSM
        let t_rhs_start = Instant::now();
        let e_original_r = &input_padded_r[..n_input];

        #[cfg(feature = "parallel")]
        let (c1_affine_r, c2_affine_r) = rayon::join(
            || G::normalize_batch(&c1_orig),
            || G::normalize_batch(&c2_orig),
        );
        #[cfg(not(feature = "parallel"))]
        let (c1_affine_r, c2_affine_r) =
            (G::normalize_batch(&c1_orig), G::normalize_batch(&c2_orig));

        #[cfg(feature = "parallel")]
        let c_combined = {
            let (m1, m2) = rayon::join(
                || G::msm(&c1_affine_r, e_original_r).expect("MSM 1"),
                || G::msm(&c2_affine_r, e_original_r).expect("MSM 2"),
            );
            vec![m1, m2]
        };
        #[cfg(not(feature = "parallel"))]
        let c_combined = vec![
            G::msm(&c1_affine_r, e_original_r).expect("MSM 1"),
            G::msm(&c2_affine_r, e_original_r).expect("MSM 2"),
        ];

        let t_rhs = t_rhs_start.elapsed();

        // [4] Verify
        let t_verify_start = Instant::now();
        let mut verifier_transcript = Transcript::new(b"MAYA-Shuffle-v1");
        let result = KShuffleGadget::verify(
            &v_pc_gens,
            &v_bp_gens,
            &mut verifier_transcript,
            &proof_r,
            &input_padded_r,
            out_commitment_r,
            &c1_prime_r,
            &c2_prime_r,
            &c_combined,
        );
        assert!(
            result.is_ok(),
            "Verification failed N={}/k={}/d={}: {:?}",
            n_input,
            k,
            d,
            result.err()
        );
        let t_verify = t_verify_start.elapsed();

        // PRINT TIMINGS 
        let ms = |dur: std::time::Duration| dur.as_secs_f64() * 1000.0;
        let t_gen_ms = ms(t_gen);
        let t_table_ms = ms(t_table);
        let t_shuffle_ms = ms(t_shuffle);
        let t_rerand_ms = ms(t_rerand);
        let t_e_prover_ms = ms(t_e_prover);
        let t_proof_gen_ms = ms(t_proof_gen);
        let t_file_read_ms = ms(t_file_read);
        let t_file_write_ms = ms(t_file_write);
        let t_v_gen_ms = ms(t_v_gen);
        let t_e_derive_ms = ms(t_e_derive);
        let t_rhs_ms = ms(t_rhs);
        let t_verify_ms = ms(t_verify);
        let t_v_file_read_ms = ms(t_v_file_read);
        let total_prover = t_gen_ms + t_table_ms + t_shuffle_ms + t_rerand_ms
            + t_e_prover_ms + t_proof_gen_ms;
        let file_io = t_file_read_ms + t_file_write_ms;
        let total_prover_e2e = total_prover + file_io;
        let total_verifier = t_v_gen_ms + t_e_derive_ms + t_rhs_ms + t_verify_ms;
        let total_verifier_e2e = t_v_file_read_ms + total_verifier;
        let proof_kb = proof_size as f64 / 1024.0;
        let thread_label = if cfg!(feature = "parallel") { "multi-threaded" } else { "single-threaded" };

        println!();
        println!("================================================================");
        println!(
            "  Config [{}/{}]: N={:>9}  k={}  d={}  ({})",
            i + 1, configs.len(), n_input, k, d, thread_label
        );
        println!("================================================================");
        println!();
        println!("  Single-run timings (one pass for quick timing):");
        println!();
        println!("  PROVER:");
        println!("    CRS generation:               {:>14.2} ms", t_gen_ms);
        println!("    Fixed-base table:             {:>14.2} ms", t_table_ms);
        println!("    Permutation:                  {:>14.2} ms", t_shuffle_ms);
        println!("    Rerandomization:              {:>14.2} ms", t_rerand_ms);
        println!("    Challenge e derivation:       {:>14.2} ms", t_e_prover_ms);
        println!("    Proof generation (*):         {:>14.2} ms", t_proof_gen_ms);
        println!("    ─────────────────────────────────────────────────");
        println!("    Total (excl. I/O):            {:>14.2} ms", total_prover);
        println!("    File I/O (read+write):        {:>14.2} ms", file_io);
        println!("    Total E2E (incl. I/O):        {:>14.2} ms", total_prover_e2e);
        println!();
        println!();
        println!("  VERIFIER:");
        println!("    CRS regeneration:             {:>14.2} ms", t_v_gen_ms);
        println!("    Challenge e derivation:       {:>14.2} ms", t_e_derive_ms);
        println!("    RHS computation (Eq. 6):      {:>14.2} ms", t_rhs_ms);
        println!("    Proof verification (*):       {:>14.2} ms", t_verify_ms);
        println!("    ────────────────────────────────────────────────");
        println!("    Total (excl. I/O):            {:>14.2} ms", total_verifier);
        println!("    File I/O (read):              {:>14.2} ms", t_v_file_read_ms);
        println!("    Total E2E (incl. I/O):        {:>14.2} ms", total_verifier_e2e);
        println!();
        println!("  Verification: PASSED");
        println!("  Proof size: {} bytes ({:.2} KB)", proof_size, proof_kb);
        println!();
        println!();
        if CRITERION_ENABLED {
            println!("  *  Proof generation and verification times can vary across runs");
            println!("     due to variable-time multi-scalar multiplications. Computing");
            println!("     their average over multiple samples for more stable estimates:");
            println!();
            println!("  Proof generation time via Criterions ({} samples, adjust SAMPLES if needed)...", SAMPLES);
        }

        // CRITERION: Prover 
        {
            let label = format!("maya-p256/iterative/prover/n={}/k={}/d={}", n_input, k, d);

            let mut rng_b = rand::thread_rng();
            let c1_b: Vec<G> = (0..n_input).map(|_| G::rand(&mut rng_b)).collect();
            let c2_b: Vec<G> = (0..n_input).map(|_| G::rand(&mut rng_b)).collect();
            let mut idx_b: Vec<usize> = (0..n_input).collect();
            idx_b.shuffle(&mut rng_b);

            #[cfg(all(feature = "parallel", not(feature = "production")))]
            let rv_b: Vec<Fr> = (0..n_input).map(|j| deterministic_rand_fr(j)).collect();
            #[cfg(not(feature = "parallel"))]
            let rv_b: Vec<Fr> = (0..n_input).map(|_| Fr::rand(&mut rng_b)).collect();

            #[cfg(feature = "parallel")]
            let (c1p_b, c2p_b) = {
                let mut a: Vec<G> = idx_b.iter().map(|&i| c1_b[i]).collect();
                let mut bv: Vec<G> = idx_b.iter().map(|&i| c2_b[i]).collect();
                a.par_iter_mut()
                    .zip(bv.par_iter_mut())
                    .zip(rv_b.par_iter())
                    .for_each(|((x, y), r)| {
                        *x += g_table.mul(r);
                        *y += f_table.mul(r);
                    });
                (a, bv)
            };
            #[cfg(not(feature = "parallel"))]
            let (c1p_b, c2p_b) = {
                let mut a: Vec<G> = idx_b.iter().map(|&i| c1_b[i]).collect();
                let mut bv: Vec<G> = idx_b.iter().map(|&i| c2_b[i]).collect();
                for (j, r) in rv_b.iter().enumerate() {
                    a[j] += g_table.mul(r);
                    bv[j] += f_table.mul(r);
                }
                (a, bv)
            };

            let c1_b_bytes = batch_serialize_compressed(&c1_b);
            let c2_b_bytes = batch_serialize_compressed(&c2_b);
            let c1p_b_bytes = batch_serialize_compressed(&c1p_b);
            let c2p_b_bytes = batch_serialize_compressed(&c2p_b);
            let inp_b = derive_challenge_e(
                &pc_gens,
                &bp_gens,
                &c1_b_bytes,
                &c2_b_bytes,
                &c1p_b_bytes,
                &c2p_b_bytes,
                n_input,
                circuit_n,
            );
            let mut out_b: Vec<Fr> = idx_b.iter().map(|&i| inp_b[i]).collect();
            out_b.resize(circuit_n, Fr::zero());
            let rp_b: Fr = -(0..n_input).map(|j| rv_b[j] * inp_b[idx_b[j]]).sum::<Fr>();

            c.bench_function(&label, |b| {
                b.iter(|| {
                    let mut t = Transcript::new(b"MAYA-Shuffle-v1");
                    let mut bench_rng = rand::thread_rng();
                    KShuffleGadget::prove(
                        &pc_gens,
                        &bp_gens,
                        &mut t,
                        &inp_b,
                        &out_b,
                        &c1p_b,
                        &c2p_b,
                        rp_b,
                        k,
                        d,
                        &mut bench_rng,
                    )
                    .expect("prover bench failed");
                });
            });
        }

        if CRITERION_ENABLED {
            println!("  Proof verification time via Criterions ({} samples, adjust SAMPLES if needed)...", SAMPLES);
        }

        // CRITERION: Verifier 
        {
            let label = format!("maya-p256/iterative/verifier/n={}/k={}/d={}", n_input, k, d);

            let mut rng_v = rand::thread_rng();
            let c1_v: Vec<G> = (0..n_input).map(|_| G::rand(&mut rng_v)).collect();
            let c2_v: Vec<G> = (0..n_input).map(|_| G::rand(&mut rng_v)).collect();
            let mut idx_v: Vec<usize> = (0..n_input).collect();
            idx_v.shuffle(&mut rng_v);

            #[cfg(all(feature = "parallel", not(feature = "production")))]
            let rv_v: Vec<Fr> = (0..n_input).map(|j| deterministic_rand_fr(j)).collect();
            #[cfg(not(feature = "parallel"))]
            let rv_v: Vec<Fr> = (0..n_input).map(|_| Fr::rand(&mut rng_v)).collect();

            #[cfg(feature = "parallel")]
            let (c1p_v, c2p_v) = {
                let mut a: Vec<G> = idx_v.iter().map(|&i| c1_v[i]).collect();
                let mut bv: Vec<G> = idx_v.iter().map(|&i| c2_v[i]).collect();
                a.par_iter_mut()
                    .zip(bv.par_iter_mut())
                    .zip(rv_v.par_iter())
                    .for_each(|((x, y), r)| {
                        *x += g_table.mul(r);
                        *y += f_table.mul(r);
                    });
                (a, bv)
            };
            #[cfg(not(feature = "parallel"))]
            let (c1p_v, c2p_v) = {
                let mut a: Vec<G> = idx_v.iter().map(|&i| c1_v[i]).collect();
                let mut bv: Vec<G> = idx_v.iter().map(|&i| c2_v[i]).collect();
                for (j, r) in rv_v.iter().enumerate() {
                    a[j] += g_table.mul(r);
                    bv[j] += f_table.mul(r);
                }
                (a, bv)
            };

            let c1_v_bytes = batch_serialize_compressed(&c1_v);
            let c2_v_bytes = batch_serialize_compressed(&c2_v);
            let c1p_v_bytes = batch_serialize_compressed(&c1p_v);
            let c2p_v_bytes = batch_serialize_compressed(&c2p_v);
            let inp_v = derive_challenge_e(
                &pc_gens,
                &bp_gens,
                &c1_v_bytes,
                &c2_v_bytes,
                &c1p_v_bytes,
                &c2p_v_bytes,
                n_input,
                circuit_n,
            );
            let mut out_v: Vec<Fr> = idx_v.iter().map(|&i| inp_v[i]).collect();
            out_v.resize(circuit_n, Fr::zero());
            let rp_v: Fr = -(0..n_input).map(|j| rv_v[j] * inp_v[idx_v[j]]).sum::<Fr>();

            let e_v = &inp_v[..n_input];
            #[cfg(feature = "parallel")]
            let (c1v_aff, c2v_aff) =
                rayon::join(|| G::normalize_batch(&c1_v), || G::normalize_batch(&c2_v));
            #[cfg(not(feature = "parallel"))]
            let (c1v_aff, c2v_aff) = (G::normalize_batch(&c1_v), G::normalize_batch(&c2_v));

            #[cfg(feature = "parallel")]
            let c_comb_v = {
                let (m1, m2) = rayon::join(
                    || G::msm(&c1v_aff, e_v).expect("MSM 1"),
                    || G::msm(&c2v_aff, e_v).expect("MSM 2"),
                );
                vec![m1, m2]
            };
            #[cfg(not(feature = "parallel"))]
            let c_comb_v = vec![
                G::msm(&c1v_aff, e_v).expect("MSM 1"),
                G::msm(&c2v_aff, e_v).expect("MSM 2"),
            ];

            let mut pt = Transcript::new(b"MAYA-Shuffle-v1");
            let mut setup_rng = rand::thread_rng();
            let (proof_v, out_com_v) = KShuffleGadget::prove(
                &pc_gens,
                &bp_gens,
                &mut pt,
                &inp_v,
                &out_v,
                &c1p_v,
                &c2p_v,
                rp_v,
                k,
                d,
                &mut setup_rng,
            )
            .expect("prove for verifier bench failed");

            c.bench_function(&label, |b| {
                b.iter(|| {
                    let mut t = Transcript::new(b"MAYA-Shuffle-v1");
                    let res = KShuffleGadget::verify(
                        &pc_gens,
                        &bp_gens,
                        &mut t,
                        &proof_v,
                        &inp_v,
                        out_com_v.clone(),
                        &c1p_v,
                        &c2p_v,
                        &c_comb_v,
                    );
                    assert!(res.is_ok(), "verifier bench failed: {:?}", res.err());
                });
            });
        }
        results.push(RunResult {
            n: n_input,
            k,
            d,
            total_prover_ms: total_prover,
            total_verifier_ms: total_verifier,
            proof_bytes: proof_size,
            proof_gen_ms: t_proof_gen_ms,
            verify_ms: t_verify_ms,
        });
    }

    println!();
    println!("================================================================");
    println!("  All {} configs completed.", configs.len());
    println!("================================================================");

    // SUMMARY TABLE 

    let read_criterion_mean_ms = |n: usize, k: usize, d: usize, role: &str| -> Option<f64> {
        let dir_name = format!(
            "maya-p256_iterative_{}_n={}_k={}_d={}",
            role, n, k, d
        );
        let json_path = format!(
            "target/criterion/{}/new/estimates.json",
            dir_name
        );
        let content = match std::fs::read_to_string(&json_path) {
            Ok(c) => c,
            Err(_) => {
                eprintln!("  [criterion] Could not read: {}", json_path);
                return None;
            }
        };
        let mean_key = "\"mean\"";
        let pe_key = "\"point_estimate\":";
        let mean_pos = content.find(mean_key)?;
        let after_mean = &content[mean_pos..];
        let pe_pos = after_mean.find(pe_key)?;
        let val_start = pe_pos + pe_key.len();
        let val_str = &after_mean[val_start..];
        let val_end = val_str.find(|c: char| c == ',' || c == '}' || c == ' ')
            .unwrap_or(val_str.len());
        let ns_value: f64 = match val_str[..val_end].trim().parse() {
            Ok(v) => v,
            Err(_) => {
                eprintln!("  [criterion] Could not parse point_estimate in: {}", json_path);
                return None;
            }
        };
        Some(ns_value / 1_000_000.0)
    };

    let thread_label_summary = if cfg!(feature = "parallel") { "multi-threaded" } else { "single-threaded" };

    let criterion_available = results.iter().any(|r|
        read_criterion_mean_ms(r.n, r.k, r.d, "prover").is_some()
    );

    let averaged_prover = |r: &RunResult| -> f64 {
        match read_criterion_mean_ms(r.n, r.k, r.d, "prover") {
            Some(crit_ms) => crit_ms + (r.total_prover_ms - r.proof_gen_ms),
            None => r.total_prover_ms,
        }
    };
    let averaged_verifier = |r: &RunResult| -> f64 {
        match read_criterion_mean_ms(r.n, r.k, r.d, "verifier") {
            Some(crit_ms) => crit_ms + (r.total_verifier_ms - r.verify_ms),
            None => r.total_verifier_ms,
        }
    };

    if quick_mode {
        if let Some(r) = results.first() {
            let p_ms = averaged_prover(r);
            let v_ms = averaged_verifier(r);
            println!();
            println!("================================================================");
            println!("  Quick-check result - N={}, k={}", r.n, r.k);
            println!();
            println!("  Criterion reports the slope estimate on screen by default (linear");
            println!("  regression of time vs iteration count). The summary table");
            println!("  below uses the mean from target/criterion/*/new/estimates.json,");
            println!("  which is the arithmetic average per-iteration time.");
            println!("  Both differ by ~1%.");
            println!("================================================================");
            println!();
            println!("  Prover (excl. I/O):    {:>10.2} ms", p_ms);
            println!("  Verifier (excl. I/O):  {:>10.2} ms", v_ms);
            println!("  Proof size:            {:>10} bytes", r.proof_bytes);
            println!();
            println!("  Build verification passed.");
            println!("================================================================");
        }
    } else {
        println!();
        println!("================================================================");
        if criterion_available {
            println!("  Summary - {}", thread_label_summary);
            println!();
            println!("  Criterion reports the slope estimate on screen by default (linear");
            println!("  regression of time vs iteration count). The summary table");
            println!("  below uses the mean from target/criterion/*/new/estimates.json,");
            println!("  which is the arithmetic average per-iteration time.");
            println!("  Both differ by ~1%.");
        } else {
            println!("  Summary - {} (single-run)", thread_label_summary);
            println!("  Note: Criterion data could not be found in target/criterion/.");
            println!("  Values below are from a single execution.");
        }
        println!("================================================================");
        println!();

        let mut ns: Vec<usize> = results.iter().map(|r| r.n).collect();
        ns.dedup();
        let ks: &[usize] = &[2, 4];

        let get_result = |n: usize, k: usize| -> Option<&RunResult> {
            results.iter().find(|r| r.n == n && r.k == k)
        };

        println!("  Prover (ms):");
        print!("  {:>12}", "n");
        for &k in ks { print!("  {:>14}", format!("k={}", k)); }
        println!();
        print!("  {:>12}", "------------");
        for _ in ks { print!("  {:>14}", "--------------"); }
        println!();
        for &n in &ns {
            print!("  {:>12}", n);
            for &k in ks {
                match get_result(n, k) {
                    Some(r) => print!("  {:>14.2}", averaged_prover(r)),
                    None => print!("  {:>14}", "—"),
                }
            }
            println!();
        }

        println!();
        println!("  Verifier (ms):");
        print!("  {:>12}", "n");
        for &k in ks { print!("  {:>14}", format!("k={}", k)); }
        println!();
        print!("  {:>12}", "------------");
        for _ in ks { print!("  {:>14}", "--------------"); }
        println!();
        for &n in &ns {
            print!("  {:>12}", n);
            for &k in ks {
                match get_result(n, k) {
                    Some(r) => print!("  {:>14.2}", averaged_verifier(r)),
                    None => print!("  {:>14}", "—"),
                }
            }
            println!();
        }

        println!();
        println!("  Proof size (bytes):");
        print!("  {:>12}", "n");
        for &k in ks { print!("  {:>14}", format!("k={}", k)); }
        println!();
        print!("  {:>12}", "------------");
        for _ in ks { print!("  {:>14}", "--------------"); }
        println!();
        for &n in &ns {
            print!("  {:>12}", n);
            for &k in ks {
                match get_result(n, k) {
                    Some(r) => print!("  {:>14}", r.proof_bytes),
                    None => print!("  {:>14}", "—"),
                }
            }
            println!();
        }
        println!();
    }

}

criterion_group! {
    name = benches;
    config = Criterion::default()
        .sample_size(SAMPLES)
        .measurement_time(std::time::Duration::from_secs(30));
    targets = custom_benchmark
}

//--- Multi-run averaging benchmark --- 
#[allow(unused_variables)]
fn full_averaging_benchmark(_c: &mut Criterion) {
    if std::env::var("BENCH_FULL_AVG").is_err() {
        return;
    }

    let num_runs: usize = std::env::var("NUM_RUNS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(10);

    let configs: &[(usize, usize)] = &[
        (1_000, 2), (1_000, 4),
        (10_000, 2), (10_000, 4),
        (100_000, 2), (100_000, 4),
        (1_000_000, 2), (1_000_000, 4),
    ];

    println!();
    println!("================================================================");
    println!("  Multi-run averaging benchmark (MAYA-P256)");
    println!("  {} runs per configuration", num_runs);
    println!("  Timing the complete pipeline (excl. file I/O)");
    println!();
    println!("  Features: {}", if cfg!(feature = "parallel") { "multi-threaded" } else { "single-threaded" });
    println!("================================================================");
    println!();

    for &(n_input, k) in configs {
        let n_padded = n_input + (k - 1) + 1;

        #[cfg(feature = "parallel")]
        let (pc_gens, bp_gens) = rayon::join(
            || PedersenGens::<G>::default(),
            || BulletproofGens::<G>::new(n_padded, 1),
        );
        #[cfg(not(feature = "parallel"))]
        let pc_gens = PedersenGens::<G>::default();
        #[cfg(not(feature = "parallel"))]
        let bp_gens = BulletproofGens::<G>::new(n_padded, 1);

        let g = pc_gens.B;
        let f = pc_gens.F;
        let g_table = FixedBaseTable::create(&g, 5);
        let f_table = FixedBaseTable::create(&f, 5);

        let rem = n_input % k;
        let circuit_n = if rem == 0 { n_input } else { n_input + (k - rem) };
        let mut n_j = circuit_n;
        let mut d = 0usize;
        while n_j > 1 {
            let r = n_j % k;
            let p = if r == 0 { 0 } else { k - r };
            n_j = (n_j + p) / k;
            d += 1;
        }

        let mut rng = rand::thread_rng();
        let c1_raw: Vec<G> = (0..n_input).map(|_| G::rand(&mut rng)).collect();
        let c2_raw: Vec<G> = (0..n_input).map(|_| G::rand(&mut rng)).collect();
        let c1_bytes = batch_serialize_compressed(&c1_raw);
        let c2_bytes = batch_serialize_compressed(&c2_raw);

        let mut prover_times: Vec<f64> = Vec::with_capacity(num_runs);
        let mut verifier_times: Vec<f64> = Vec::with_capacity(num_runs);

        for run in 0..num_runs {
            // Full prover pipeline 
            let t_prover_start = Instant::now();

            #[cfg(feature = "parallel")]
            let (run_pc, run_bp) = rayon::join(
                || PedersenGens::<G>::default(),
                || BulletproofGens::<G>::new(n_padded, 1),
            );
            #[cfg(not(feature = "parallel"))]
            let run_pc = PedersenGens::<G>::default();
            #[cfg(not(feature = "parallel"))]
            let run_bp = BulletproofGens::<G>::new(n_padded, 1);

            let run_g = run_pc.B;
            let run_f = run_pc.F;
            let run_g_table = FixedBaseTable::create(&run_g, 5);
            let run_f_table = FixedBaseTable::create(&run_f, 5);

            let mut indices: Vec<usize> = (0..n_input).collect();
            indices.shuffle(&mut rng);

            #[cfg(all(feature = "parallel", not(feature = "production")))]
            let rv: Vec<Fr> = (0..n_input).map(|j| deterministic_rand_fr(j)).collect();
            #[cfg(not(feature = "parallel"))]
            let rv: Vec<Fr> = (0..n_input).map(|_| Fr::rand(&mut rng)).collect();

            #[cfg(feature = "parallel")]
            let (c1_prime, c2_prime) = {
                let mut c1p: Vec<G> = indices.iter().map(|&i| c1_raw[i]).collect();
                let mut c2p: Vec<G> = indices.iter().map(|&i| c2_raw[i]).collect();
                c1p.par_iter_mut()
                    .zip(c2p.par_iter_mut())
                    .zip(rv.par_iter())
                    .for_each(|((a, b), r)| { *a += run_g_table.mul(r); *b += run_f_table.mul(r); });
                (c1p, c2p)
            };
            #[cfg(not(feature = "parallel"))]
            let (c1_prime, c2_prime) = {
                let mut c1p: Vec<G> = indices.iter().map(|&i| c1_raw[i]).collect();
                let mut c2p: Vec<G> = indices.iter().map(|&i| c2_raw[i]).collect();
                for (j, r) in rv.iter().enumerate() {
                    c1p[j] += run_g_table.mul(r);
                    c2p[j] += run_f_table.mul(r);
                }
                (c1p, c2p)
            };

            let c1p_bytes = batch_serialize_compressed(&c1_prime);
            let c2p_bytes = batch_serialize_compressed(&c2_prime);
            let input_padded = derive_challenge_e(
                &run_pc, &run_bp, &c1_bytes, &c2_bytes, &c1p_bytes, &c2p_bytes, n_input, circuit_n,
            );
            let mut output_padded: Vec<Fr> = indices.iter().map(|&i| input_padded[i]).collect();
            output_padded.resize(circuit_n, Fr::zero());
            let r_prime: Fr = -(0..n_input).map(|j| rv[j] * input_padded[indices[j]]).sum::<Fr>();

            let mut pt = Transcript::new(b"MAYA-Shuffle-v1");
            let (proof, out_commitment) = KShuffleGadget::prove(
                &run_pc, &run_bp, &mut pt,
                &input_padded, &output_padded,
                &c1_prime, &c2_prime,
                r_prime, k, d, &mut rng,
            ).expect("full_avg: prove failed");

            let prover_ms = t_prover_start.elapsed().as_secs_f64() * 1000.0;
            prover_times.push(prover_ms);

            // Full verifier pipeline 
            let t_verifier_start = Instant::now();

            #[cfg(feature = "parallel")]
            let (v_pc, v_bp) = rayon::join(
                || PedersenGens::<G>::default(),
                || BulletproofGens::<G>::new(n_padded, 1),
            );
            #[cfg(not(feature = "parallel"))]
            let v_pc = PedersenGens::<G>::default();
            #[cfg(not(feature = "parallel"))]
            let v_bp = BulletproofGens::<G>::new(n_padded, 1);

            let input_padded_v = derive_challenge_e(
                &v_pc, &v_bp, &c1_bytes, &c2_bytes, &c1p_bytes, &c2p_bytes, n_input, circuit_n,
            );
            let e_v = &input_padded_v[..n_input];
            let c1v_aff = G::normalize_batch(&c1_raw);
            let c2v_aff = G::normalize_batch(&c2_raw);

            #[cfg(feature = "parallel")]
            let c_combined = {
                let (m1, m2) = rayon::join(
                    || G::msm(&c1v_aff, e_v).expect("MSM 1"),
                    || G::msm(&c2v_aff, e_v).expect("MSM 2"),
                );
                vec![m1, m2]
            };
            #[cfg(not(feature = "parallel"))]
            let c_combined = vec![
                G::msm(&c1v_aff, e_v).expect("MSM 1"),
                G::msm(&c2v_aff, e_v).expect("MSM 2"),
            ];

            let mut vt = Transcript::new(b"MAYA-Shuffle-v1");
            let res = KShuffleGadget::verify(
                &v_pc, &v_bp, &mut vt, &proof,
                &input_padded_v, out_commitment,
                &c1_prime, &c2_prime, &c_combined,
            );
            assert!(res.is_ok(), "full_avg: verify failed N={}/k={}/d={}", n_input, k, d);

            let verifier_ms = t_verifier_start.elapsed().as_secs_f64() * 1000.0;
            verifier_times.push(verifier_ms);

            println!("  Run {}/{}: N={} k={} prover={:.2}ms verifier={:.2}ms",
                run + 1, num_runs, n_input, k, prover_ms, verifier_ms);
        }

        let p_mean = prover_times.iter().sum::<f64>() / num_runs as f64;
        let v_mean = verifier_times.iter().sum::<f64>() / num_runs as f64;
        let p_std = if num_runs > 1 {
            (prover_times.iter().map(|t| (t - p_mean).powi(2)).sum::<f64>() / (num_runs - 1) as f64).sqrt()
        } else { 0.0 };
        let v_std = if num_runs > 1 {
            (verifier_times.iter().map(|t| (t - v_mean).powi(2)).sum::<f64>() / (num_runs - 1) as f64).sqrt()
        } else { 0.0 };

        println!();
        println!("  N={} k={}: Prover  mean={:.2}ms  std={:.2}ms", n_input, k, p_mean, p_std);
        println!("  N={} k={}: Verifier mean={:.2}ms  std={:.2}ms", n_input, k, v_mean, v_std);
        println!();
    }
}

// full_averaging_benchmark does its own Instant loop, 
// but Criterion still needs a valid group config.
criterion_group! {
    name = full_avg_bench;
    config = Criterion::default().sample_size(10);
    targets = full_averaging_benchmark
}
criterion_main!(benches, full_avg_bench);
