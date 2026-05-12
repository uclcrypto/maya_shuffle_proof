// MAYA-Ristretto Benchmark - Ristretto255

extern crate maya_ristretto;
use maya_ristretto::r1cs::LinearCombination;
use maya_ristretto::r1cs::{ConstraintSystem, Prover, R1CSError, R1CSProof, Variable, Verifier};
use maya_ristretto::transcript::TranscriptProtocol;
use maya_ristretto::{BulletproofGens, PedersenGens};

#[macro_use]
extern crate criterion;
use criterion::Criterion;

extern crate curve25519_dalek;
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoBasepointTable, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::VartimeMultiscalarMul;

extern crate merlin;
use merlin::Transcript;

extern crate rand;
use rand::seq::SliceRandom;
use rand::SeedableRng;

extern crate rand_chacha;
use rand_chacha::ChaCha20Rng;

extern crate bincode;

use std::fs::File;
use std::io::{BufReader, BufWriter, Read, Write};
use std::time::Instant;

#[cfg(feature = "parallel")]
extern crate rayon;
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

// --- Padding helpers ---
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

// --- Shuffle Gadget ---
struct KShuffleGadget;

impl KShuffleGadget {
    fn fill_cs<CS: ConstraintSystem>(cs: &mut CS, x: &[Variable], y: &[Scalar], k_original: usize) {
        let z = cs.challenge_scalar(b"k-scalar shuffle challenge");
        let k = x.len();
        assert_eq!(x.len(), y.len());

        let mut prod_y = Scalar::ONE;
        for yi in y {
            prod_y *= *yi - z;
        }

        let mut prev_lc = if k_original == 0 {
            cs.constrain(x[0] - Scalar::ZERO);
            LinearCombination::from(-z)
        } else {
            x[0] - z
        };

        for i in 1..k {
            if i >= k_original {
                cs.constrain(x[i] - Scalar::ZERO);
                prev_lc = prev_lc * (-z);
            } else {
                let term = x[i] - z;
                let (_, _, out_var) = cs.multiply(prev_lc, term);
                prev_lc = LinearCombination::from(out_var);
            }
        }
        cs.constrain(prev_lc - prod_y);
    }

    pub fn prove<'a, 'b>(
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut Transcript,
        input: &[Scalar],
        output: &[Scalar],
        c1_prime: &[RistrettoPoint],
        c2_prime: &[RistrettoPoint],
        r_prime: Scalar,
        k_fold: usize,
        num_rounds: usize,
        rng: &mut (impl rand::RngCore + rand::CryptoRng),
    ) -> Result<(R1CSProof, CompressedRistretto), R1CSError> {
        let k = input.len();
        let k_original = c1_prime.len();
        if k <= 1 {
            return Err(R1CSError::InputLengthError);
        }

        transcript.append_message(b"dom-sep", b"ShuffleProof");
        transcript.append_message(b"k", Scalar::from(k as u64).as_bytes());

        let mut prover = Prover::new(bp_gens, pc_gens, transcript);
        let v_blinding = Scalar::random(rng);
        let (output_commitment, output_vars) = prover.commit_vec(output, v_blinding, k_original);
        let mut cs = prover.finalize_inputs();
        Self::fill_cs(&mut cs, &output_vars, input, k_original);
        let proof = cs.prove(c1_prime, c2_prime, r_prime, k_fold, num_rounds)?;
        Ok((proof, output_commitment))
    }

    pub fn verify<'a, 'b>(
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut Transcript,
        proof: &R1CSProof,
        input: &[Scalar],
        output_commitment: CompressedRistretto,
        c1_prime: &[RistrettoPoint],
        c2_prime: &[RistrettoPoint],
        c_combined: &[RistrettoPoint],
    ) -> Result<(), R1CSError> {
        let k = input.len();
        transcript.append_message(b"dom-sep", b"ShuffleProof");
        transcript.append_message(b"k", Scalar::from(k as u64).as_bytes());

        let mut verifier = Verifier::new(bp_gens, pc_gens, transcript);
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
    pc_gens: &PedersenGens,
    bp_gens: &BulletproofGens,
    c1_bytes: &[u8],
    c2_bytes: &[u8],
    c1p_bytes: &[u8],
    c2p_bytes: &[u8],
    n_original: usize,
    n_padded: usize,
) -> Vec<Scalar> {
    let verbose = std::env::var("VERBOSE").ok()
        .filter(|v| v == "1" || v.eq_ignore_ascii_case("true"))
        .is_some();
    let mut ts = Transcript::new(b"FiatShamir-e");
    ts.append_message(b"dom-sep", b"challenge-e-derivation");

    ts.commit_point(b"pk_g", &pc_gens.B.compress());
    ts.commit_point(b"pk_f", &pc_gens.F.compress());
    ts.commit_point(b"ck_h", &pc_gens.B_blinding.compress());

    <Transcript as TranscriptProtocol>::commit_u64(&mut ts, b"ck_n", bp_gens.gens_capacity as u64);
    if let Some(g0) = bp_gens.G_vec.get(0).and_then(|v| v.get(0)) {
        ts.commit_point(b"ck_g0", &g0.compress());
    }
    if let Some(h0) = bp_gens.H_vec.get(0).and_then(|v| v.get(0)) {
        ts.commit_point(b"ck_h0", &h0.compress());
    }

    let t_transcript = Instant::now();
    for chunk in c1_bytes.chunks(32) {
        ts.append_message(b"c1", chunk);
    }
    for chunk in c2_bytes.chunks(32) {
        ts.append_message(b"c2", chunk);
    }
    for chunk in c1p_bytes.chunks(32) {
        ts.append_message(b"c1p", chunk);
    }
    for chunk in c2p_bytes.chunks(32) {
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
    let mut e: Vec<Scalar> = (0..n_original).map(|_| Scalar::random(&mut prg)).collect();
    e.resize(n_padded, Scalar::ZERO);
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
fn deterministic_rand_scalar(index: usize) -> Scalar {
    use rand::SeedableRng;
    let mut seed = [0u8; 32];
    seed[..8].copy_from_slice(&(index as u64).to_le_bytes());
    seed[8..16].copy_from_slice(&0xCAFEu64.to_le_bytes()); 
    let mut rng = rand::rngs::StdRng::from_seed(seed);
    Scalar::random(&mut rng)
}

// --- File I/O Helpers ---
fn write_ciphertexts(
    path: &str,
    c1: &[RistrettoPoint],
    c2: &[RistrettoPoint],
    g: &RistrettoPoint,
    f: &RistrettoPoint,
    h: &RistrettoPoint,
) -> std::io::Result<usize> {
    let n = c1.len();
    assert_eq!(n, c2.len());
    let file = File::create(path)?;
    let mut w = BufWriter::new(file);
    w.write_all(&(n as u64).to_le_bytes())?;

    #[cfg(feature = "parallel")]
    {
        let (c1_blob, c2_blob) = rayon::join(|| batch_compress(c1), || batch_compress(c2));
        w.write_all(&c1_blob)?;
        w.write_all(&c2_blob)?;
    }
    #[cfg(not(feature = "parallel"))]
    for pt in c1.iter().chain(c2.iter()) {
        w.write_all(pt.compress().as_bytes())?;
    }

    w.write_all(g.compress().as_bytes())?;
    w.write_all(f.compress().as_bytes())?;
    w.write_all(h.compress().as_bytes())?;

    w.flush()?;
    let fh = w.into_inner()?;
    fh.sync_all()?;
    Ok(std::fs::metadata(path)?.len() as usize)
}

fn read_ciphertexts(
    path: &str,
) -> std::io::Result<(
    Vec<RistrettoPoint>,
    Vec<RistrettoPoint>,
    RistrettoPoint,
    RistrettoPoint,
    RistrettoPoint,
    Vec<u8>,
    Vec<u8>,
)> {
    let file = File::open(path)?;
    let mut r = BufReader::new(file);
    let mut buf8 = [0u8; 8];
    r.read_exact(&mut buf8)?;
    let n = u64::from_le_bytes(buf8) as usize;

    
    #[cfg(feature = "parallel")]
    let (c1, c2, c1_raw, c2_raw) = {
        let mut blob = vec![0u8; 2 * n * 32];
        r.read_exact(&mut blob)?;
        let mid = n * 32;
        let c1_raw = blob[..mid].to_vec();
        let c2_raw = blob[mid..].to_vec();
        let (c1_blob, c2_blob) = blob.split_at(mid);
        let (c1r, c2r) = rayon::join(|| batch_decompress(c1_blob), || batch_decompress(c2_blob));
        (c1r?, c2r?, c1_raw, c2_raw)
    };
    #[cfg(not(feature = "parallel"))]
    let (c1, c2, c1_raw, c2_raw) = {
        let mut c1 = Vec::with_capacity(n);
        let mut c2 = Vec::with_capacity(n);
        let mut c1_raw = Vec::with_capacity(n * 32);
        let mut c2_raw = Vec::with_capacity(n * 32);
        let mut buf32 = [0u8; 32];
        for _ in 0..n {
            r.read_exact(&mut buf32)?;
            c1_raw.extend_from_slice(&buf32);
            c1.push(
                CompressedRistretto::from_slice(&buf32)
                    .map_err(|e| {
                        std::io::Error::new(std::io::ErrorKind::InvalidData, format!("{}", e))
                    })?
                    .decompress()
                    .ok_or_else(|| {
                        std::io::Error::new(std::io::ErrorKind::InvalidData, "decompress failed")
                    })?,
            );
        }
        for _ in 0..n {
            r.read_exact(&mut buf32)?;
            c2_raw.extend_from_slice(&buf32);
            c2.push(
                CompressedRistretto::from_slice(&buf32)
                    .map_err(|e| {
                        std::io::Error::new(std::io::ErrorKind::InvalidData, format!("{}", e))
                    })?
                    .decompress()
                    .ok_or_else(|| {
                        std::io::Error::new(std::io::ErrorKind::InvalidData, "decompress failed")
                    })?,
            );
        }
        (c1, c2, c1_raw, c2_raw)
    };

    let mut buf32 = [0u8; 32];
    r.read_exact(&mut buf32)?;
    let g = CompressedRistretto::from_slice(&buf32)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("{}", e)))?
        .decompress()
        .ok_or_else(|| {
            std::io::Error::new(std::io::ErrorKind::InvalidData, "decompress g failed")
        })?;
    r.read_exact(&mut buf32)?;
    let f = CompressedRistretto::from_slice(&buf32)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("{}", e)))?
        .decompress()
        .ok_or_else(|| {
            std::io::Error::new(std::io::ErrorKind::InvalidData, "decompress f failed")
        })?;
    r.read_exact(&mut buf32)?;
    let h = CompressedRistretto::from_slice(&buf32)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("{}", e)))?
        .decompress()
        .ok_or_else(|| {
            std::io::Error::new(std::io::ErrorKind::InvalidData, "decompress h failed")
        })?;

    Ok((c1, c2, g, f, h, c1_raw, c2_raw))
}

#[allow(dead_code)]
fn write_scalars(path: &str, scalars: &[Scalar]) -> std::io::Result<()> {
    let file = File::create(path)?;
    let mut w = BufWriter::new(file);
    w.write_all(&(scalars.len() as u64).to_le_bytes())?;
    for s in scalars {
        w.write_all(s.as_bytes())?;
    }
    w.flush()?;
    let f = w.into_inner()?;
    f.sync_all()?;
    Ok(())
}

#[allow(dead_code)]
fn read_scalars(path: &str) -> std::io::Result<Vec<Scalar>> {
    let file = File::open(path)?;
    let mut r = BufReader::new(file);
    let mut buf8 = [0u8; 8];
    r.read_exact(&mut buf8)?;
    let n = u64::from_le_bytes(buf8) as usize;
    let mut out = Vec::with_capacity(n);
    let mut buf32 = [0u8; 32];
    for _ in 0..n {
        r.read_exact(&mut buf32)?;
        let s = Scalar::from_canonical_bytes(buf32)
            .into_option()
            .ok_or_else(|| {
                std::io::Error::new(std::io::ErrorKind::InvalidData, "invalid scalar bytes")
            })?;
        out.push(s);
    }
    Ok(out)
}


fn batch_compress(points: &[RistrettoPoint]) -> Vec<u8> {
    let mut blob = vec![0u8; points.len() * 32];
    #[cfg(feature = "parallel")]
    blob.par_chunks_exact_mut(32)
        .zip(points.par_iter())
        .for_each(|(chunk, pt)| chunk.copy_from_slice(pt.compress().as_bytes()));
    #[cfg(not(feature = "parallel"))]
    for (chunk, pt) in blob.chunks_exact_mut(32).zip(points.iter()) {
        chunk.copy_from_slice(pt.compress().as_bytes());
    }
    blob
}


fn batch_decompress(blob: &[u8]) -> std::io::Result<Vec<RistrettoPoint>> {
    assert_eq!(
        blob.len() % 32,
        0,
        "blob length must be a multiple of 32 bytes"
    );
    #[cfg(feature = "parallel")]
    {
        blob.par_chunks(32)
            .map(|chunk| {
                CompressedRistretto::from_slice(chunk)
                    .map_err(|e| {
                        std::io::Error::new(std::io::ErrorKind::InvalidData, format!("{}", e))
                    })?
                    .decompress()
                    .ok_or_else(|| {
                        std::io::Error::new(std::io::ErrorKind::InvalidData, "decompress failed")
                    })
            })
            .collect()
    }
    #[cfg(not(feature = "parallel"))]
    {
        let mut out = Vec::with_capacity(blob.len() / 32);
        for chunk in blob.chunks(32) {
            out.push(
                CompressedRistretto::from_slice(chunk)
                    .map_err(|e| {
                        std::io::Error::new(std::io::ErrorKind::InvalidData, format!("{}", e))
                    })?
                    .decompress()
                    .ok_or_else(|| {
                        std::io::Error::new(std::io::ErrorKind::InvalidData, "decompress failed")
                    })?,
            );
        }
        Ok(out)
    }
}

fn write_proof_bundle(
    path: &str,
    proof: &R1CSProof,
    out_commitment: &CompressedRistretto,
    c1p_blob: &[u8],
    c2p_blob: &[u8],
) -> std::io::Result<usize> {
    let file = File::create(path)?;
    let mut w = BufWriter::new(file);

    let proof_bytes = bincode::serialize(proof).expect("proof bincode serialize");

    w.write_all(&(proof_bytes.len() as u64).to_le_bytes())?;
    w.write_all(&proof_bytes)?;

    w.write_all(out_commitment.as_bytes())?; 

    let n1 = c1p_blob.len() / 32;
    let n2 = c2p_blob.len() / 32;
    w.write_all(&(n1 as u64).to_le_bytes())?;
    w.write_all(c1p_blob)?;
    w.write_all(&(n2 as u64).to_le_bytes())?;
    w.write_all(c2p_blob)?;

    w.flush()?;
    let f = w.into_inner()?;
    f.sync_all()?;
    Ok(std::fs::metadata(path)?.len() as usize)
}

fn read_proof_bundle(
    path: &str,
) -> std::io::Result<(
    R1CSProof,
    CompressedRistretto,
    Vec<RistrettoPoint>,
    Vec<RistrettoPoint>,
    Vec<u8>,
    Vec<u8>,
)> {
    let file = File::open(path)?;
    let mut r = BufReader::new(file);
    let mut buf8 = [0u8; 8];
    let mut buf32 = [0u8; 32];

    r.read_exact(&mut buf8)?;
    let proof_len = u64::from_le_bytes(buf8) as usize;
    let mut proof_bytes = vec![0u8; proof_len];
    r.read_exact(&mut proof_bytes)?;
    let proof: R1CSProof = bincode::deserialize(&proof_bytes).expect("proof bincode deserialize");

    r.read_exact(&mut buf32)?;
    let out_commitment = CompressedRistretto::from_slice(&buf32)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("{}", e)))?;

    
    r.read_exact(&mut buf8)?;
    let n1 = u64::from_le_bytes(buf8) as usize;
    let mut c1p_blob = vec![0u8; n1 * 32];
    r.read_exact(&mut c1p_blob)?;

    r.read_exact(&mut buf8)?;
    let n2 = u64::from_le_bytes(buf8) as usize;
    let mut c2p_blob = vec![0u8; n2 * 32];
    r.read_exact(&mut c2p_blob)?;

    #[cfg(feature = "parallel")]
    let (c1_prime, c2_prime) = {
        let (r1, r2) = rayon::join(
            || batch_decompress(&c1p_blob),
            || batch_decompress(&c2p_blob),
        );
        (r1?, r2?)
    };
    #[cfg(not(feature = "parallel"))]
    let c1_prime = batch_decompress(&c1p_blob)?;
    #[cfg(not(feature = "parallel"))]
    let c2_prime = batch_decompress(&c2p_blob)?;

    Ok((
        proof,
        out_commitment,
        c1_prime,
        c2_prime,
        c1p_blob,
        c2p_blob,
    ))
}

// --- Tables 1 and 2 - Prover and Verifier Performance---
#[allow(unused_variables)]
fn custom_benchmark(c: &mut Criterion) {
    if std::env::var("BENCH_FOLDING").is_ok()
        || std::env::var("BENCH_PADDING").is_ok()
        || std::env::var("BENCH_FULL_AVG").is_ok()
    {
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
        if fv.is_empty() {
            fv.push("none");
        }
        fv.join(", ")
    };

    println!();
    println!("================================================================");
    if quick_mode {
        println!("  MAYA-Ristretto (Ristretto255 / curve25519-dalek)");
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

    let input_ciph_path = "./maya_ristretto_bench_input_ciph.bin";
    let output_bundle_path = "./maya_ristretto_bench_output_bundle.bin";

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
        let n_padded = n_input + (k - 1) + 1; // +1 safety margin

        let t_gen_start = Instant::now();

        #[cfg(feature = "parallel")]
        let (pc_gens, bp_gens) = rayon::join(
            || PedersenGens::default(),
            || BulletproofGens::new(n_padded, 1),
        );
        #[cfg(not(feature = "parallel"))]
        let pc_gens = PedersenGens::default();
        #[cfg(not(feature = "parallel"))]
        let bp_gens = BulletproofGens::new(n_padded, 1);

        let t_gen = t_gen_start.elapsed();

        let mut rng = rand::thread_rng();

        let g = pc_gens.B;
        let f = pc_gens.F;

        let t_table_start = Instant::now();
        let g_table = RistrettoBasepointTable::create(&g);
        let f_table = RistrettoBasepointTable::create(&f);
        let t_table = t_table_start.elapsed();
        let table_size_bytes = std::mem::size_of::<RistrettoBasepointTable>();

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
        let m_final = n_j; 

        let mut total_pad = 0usize;
        let mut nj2 = n_input;
        for _ in 0..d {
            let r = nj2 % k;
            let p = if r == 0 { 0 } else { k - r };
            total_pad += p;
            nj2 = (nj2 + p) / k;
        }
        let padding_pct = total_pad as f64 / n_input as f64 * 100.0;


        let c1_raw: Vec<RistrettoPoint> = (0..n_input)
            .map(|_| RistrettoPoint::random(&mut rng))
            .collect();
        let c2_raw: Vec<RistrettoPoint> = (0..n_input)
            .map(|_| RistrettoPoint::random(&mut rng))
            .collect();

        let input_file_size = write_ciphertexts(
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
        let c1_prime_init: Vec<RistrettoPoint> = indices.iter().map(|&i| c1[i]).collect();
        let c2_prime_init: Vec<RistrettoPoint> = indices.iter().map(|&i| c2[i]).collect();
        let t_shuffle = t_shuffle_start.elapsed();

        // [3] Rerandomization + Fiat-Shamir e
        let t_rerand_start = Instant::now();

        #[cfg(all(feature = "parallel", not(feature = "production")))]
        let r_values: Vec<Scalar> = (0..n_input).map(|j| deterministic_rand_scalar(j)).collect();
        #[cfg(not(feature = "parallel"))]
        let r_values: Vec<Scalar> = (0..n_input).map(|_| Scalar::random(&mut rng)).collect();

        #[cfg(feature = "parallel")]
        let (c1_prime, c2_prime) = {
            let mut c1p = c1_prime_init;
            let mut c2p = c2_prime_init;
            c1p.par_iter_mut()
                .zip(c2p.par_iter_mut())
                .zip(r_values.par_iter())
                .for_each(|((a, b), r)| {
                    *a += &g_table * r;
                    *b += &f_table * r;
                });
            (c1p, c2p)
        };
        #[cfg(not(feature = "parallel"))]
        let (c1_prime, c2_prime) = {
            let mut c1p = c1_prime_init;
            let mut c2p = c2_prime_init;
            for (j, r) in r_values.iter().enumerate() {
                c1p[j] += &g_table * r;
                c2p[j] += &f_table * r;
            }
            (c1p, c2p)
        };

        let t_rerand = t_rerand_start.elapsed();

        let t_e_prover_start = Instant::now();
        let c1p_bytes = batch_compress(&c1_prime);
        let c2p_bytes = batch_compress(&c2_prime);
        let input_padded = derive_challenge_e(
            &pc_gens, &bp_gens, &c1_bytes, &c2_bytes, &c1p_bytes, &c2p_bytes, n_input, circuit_n,
        );
        let mut output_padded: Vec<Scalar> = indices.iter().map(|&i| input_padded[i]).collect();
        output_padded.resize(circuit_n, Scalar::ZERO);
        let r_prime: Scalar = {
            let s = (0..n_input)
                .map(|j| r_values[j] * input_padded[indices[j]])
                .fold(Scalar::ZERO, |acc, x| acc + x);
            -s
        };
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
        let output_file_size = write_proof_bundle(
            output_bundle_path,
            &proof,
            &out_commitment,
            &c1p_bytes,
            &c2p_bytes,
        )
        .expect("write_proof_bundle failed");
        let t_file_write = t_write_start.elapsed();

        let proof_size = bincode::serialize(&proof).expect("proof serialize").len();

        // SINGLE-RUN VERIFIER 

        // [0] Verifier regenerates CRS
        let t_v_gen_start = Instant::now();
        let v_pc_gens = PedersenGens::default();
        let v_bp_gens = BulletproofGens::new(n_padded, 1);
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
        let c_combined = {
            let num_threads = rayon::current_num_threads();
            let chunk_size = (n_input + num_threads - 1) / num_threads;
            let sum0: RistrettoPoint = c1_orig
                .par_chunks(chunk_size)
                .zip(e_original_r.par_chunks(chunk_size))
                .map(|(pts, scs)| RistrettoPoint::vartime_multiscalar_mul(scs.iter(), pts.iter()))
                .sum();
            let sum1: RistrettoPoint = c2_orig
                .par_chunks(chunk_size)
                .zip(e_original_r.par_chunks(chunk_size))
                .map(|(pts, scs)| RistrettoPoint::vartime_multiscalar_mul(scs.iter(), pts.iter()))
                .sum();
            vec![sum0, sum1]
        };
        #[cfg(not(feature = "parallel"))]
        let c_combined = {
            let sum0 = RistrettoPoint::vartime_multiscalar_mul(e_original_r.iter(), c1_orig.iter());
            let sum1 = RistrettoPoint::vartime_multiscalar_mul(e_original_r.iter(), c2_orig.iter());
            vec![sum0, sum1]
        };

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
            println!("  (*) Proof generation and verification times can vary across runs");
            println!("     due to variable-time multi-scalar multiplications. Computing");
            println!("     their average over multiple samples for more stable estimates:");
            println!();
            println!("  Proof generation time via Criterions ({} samples, adjust SAMPLES if needed)...", SAMPLES);
        }

        // CRITERION: Prover 
        {
            let label = format!(
                "maya-ristretto/iterative/prover/n={}/k={}/d={}",
                n_input, k, d
            );

            let mut rng_b = rand::thread_rng();
            let c1_b: Vec<RistrettoPoint> = (0..n_input)
                .map(|_| RistrettoPoint::random(&mut rng_b))
                .collect();
            let c2_b: Vec<RistrettoPoint> = (0..n_input)
                .map(|_| RistrettoPoint::random(&mut rng_b))
                .collect();
            let mut idx_b: Vec<usize> = (0..n_input).collect();
            idx_b.shuffle(&mut rng_b);

            #[cfg(all(feature = "parallel", not(feature = "production")))]
            let rv_b: Vec<Scalar> = (0..n_input).map(|j| deterministic_rand_scalar(j)).collect();
            #[cfg(not(feature = "parallel"))]
            let rv_b: Vec<Scalar> = (0..n_input).map(|_| Scalar::random(&mut rng_b)).collect();

            #[cfg(feature = "parallel")]
            let (c1p_b, c2p_b) = {
                let mut a: Vec<RistrettoPoint> = idx_b.iter().map(|&i| c1_b[i]).collect();
                let mut bv: Vec<RistrettoPoint> = idx_b.iter().map(|&i| c2_b[i]).collect();
                a.par_iter_mut()
                    .zip(bv.par_iter_mut())
                    .zip(rv_b.par_iter())
                    .for_each(|((x, y), r)| {
                        *x += &g_table * r;
                        *y += &f_table * r;
                    });
                (a, bv)
            };
            #[cfg(not(feature = "parallel"))]
            let (c1p_b, c2p_b) = {
                let mut a: Vec<RistrettoPoint> = idx_b.iter().map(|&i| c1_b[i]).collect();
                let mut bv: Vec<RistrettoPoint> = idx_b.iter().map(|&i| c2_b[i]).collect();
                for (j, r) in rv_b.iter().enumerate() {
                    a[j] += &g_table * r;
                    bv[j] += &f_table * r;
                }
                (a, bv)
            };

            let c1_b_bytes = batch_compress(&c1_b);
            let c2_b_bytes = batch_compress(&c2_b);
            let c1p_b_bytes = batch_compress(&c1p_b);
            let c2p_b_bytes = batch_compress(&c2p_b);
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
            let mut out_b: Vec<Scalar> = idx_b.iter().map(|&i| inp_b[i]).collect();
            out_b.resize(circuit_n, Scalar::ZERO);
            let rp_b: Scalar = {
                let s = (0..n_input)
                    .map(|j| rv_b[j] * inp_b[idx_b[j]])
                    .fold(Scalar::ZERO, |acc, x| acc + x);
                -s
            };

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
            let label = format!(
                "maya-ristretto/iterative/verifier/n={}/k={}/d={}",
                n_input, k, d
            );

            let mut rng_v = rand::thread_rng();
            let c1_v: Vec<RistrettoPoint> = (0..n_input)
                .map(|_| RistrettoPoint::random(&mut rng_v))
                .collect();
            let c2_v: Vec<RistrettoPoint> = (0..n_input)
                .map(|_| RistrettoPoint::random(&mut rng_v))
                .collect();
            let mut idx_v: Vec<usize> = (0..n_input).collect();
            idx_v.shuffle(&mut rng_v);

            #[cfg(all(feature = "parallel", not(feature = "production")))]
            let rv_v: Vec<Scalar> = (0..n_input).map(|j| deterministic_rand_scalar(j)).collect();
            #[cfg(not(feature = "parallel"))]
            let rv_v: Vec<Scalar> = (0..n_input).map(|_| Scalar::random(&mut rng_v)).collect();

            #[cfg(feature = "parallel")]
            let (c1p_v, c2p_v) = {
                let mut a: Vec<RistrettoPoint> = idx_v.iter().map(|&i| c1_v[i]).collect();
                let mut bv: Vec<RistrettoPoint> = idx_v.iter().map(|&i| c2_v[i]).collect();
                a.par_iter_mut()
                    .zip(bv.par_iter_mut())
                    .zip(rv_v.par_iter())
                    .for_each(|((x, y), r)| {
                        *x += &g_table * r;
                        *y += &f_table * r;
                    });
                (a, bv)
            };
            #[cfg(not(feature = "parallel"))]
            let (c1p_v, c2p_v) = {
                let mut a: Vec<RistrettoPoint> = idx_v.iter().map(|&i| c1_v[i]).collect();
                let mut bv: Vec<RistrettoPoint> = idx_v.iter().map(|&i| c2_v[i]).collect();
                for (j, r) in rv_v.iter().enumerate() {
                    a[j] += &g_table * r;
                    bv[j] += &f_table * r;
                }
                (a, bv)
            };

            let c1_v_bytes = batch_compress(&c1_v);
            let c2_v_bytes = batch_compress(&c2_v);
            let c1p_v_bytes = batch_compress(&c1p_v);
            let c2p_v_bytes = batch_compress(&c2p_v);
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
            let mut out_v: Vec<Scalar> = idx_v.iter().map(|&i| inp_v[i]).collect();
            out_v.resize(circuit_n, Scalar::ZERO);
            let rp_v: Scalar = {
                let s = (0..n_input)
                    .map(|j| rv_v[j] * inp_v[idx_v[j]])
                    .fold(Scalar::ZERO, |acc, x| acc + x);
                -s
            };

            let e_v = &inp_v[..n_input];
            let c_comb_v = {
                let sum0 = RistrettoPoint::vartime_multiscalar_mul(e_v.iter(), c1_v.iter());
                let sum1 = RistrettoPoint::vartime_multiscalar_mul(e_v.iter(), c2_v.iter());
                vec![sum0, sum1]
            };

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
                        &pc_gens, &bp_gens, &mut t, &proof_v, &inp_v, out_com_v, &c1p_v, &c2p_v,
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
            "maya-ristretto_iterative_{}_n={}_k={}_d={}",
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

// ---Table 12 - Padding Comparison (Appendix R)---
#[allow(unused_variables)]
fn padding_comparison_benchmark(c: &mut Criterion) {
    if std::env::var("BENCH_PADDING").is_err() {
        return;
    }

    println!();
    println!("================================================================");
    println!("  Padding Comparison (Table 12)");
    println!("  N = 2^20 + 1 = 1,048,577");
    println!("  Mode: {}", if cfg!(feature = "global_padding") { "Global" } else { "Iterative" });
    println!();
    println!("  Measuring proof generation time only, since this is where");
    println!("  padding strategy has the greatest impact.");
    println!("================================================================");
    println!();

    struct PaddingConfig {
        k: usize,
        d: usize,
        label: &'static str,
    }

    let configs: &[PaddingConfig] = &[
        // Tier 1: Early-stop (large m, shallow recursion)
        PaddingConfig { k: 2, d: 6,  label: "Early-stop" },
        PaddingConfig { k: 3, d: 4,  label: "Early-stop" },
        PaddingConfig { k: 4, d: 3,  label: "Early-stop" },
        PaddingConfig { k: 5, d: 3,  label: "Early-stop" },
        // Tier 2: Balanced
        PaddingConfig { k: 2, d: 10, label: "Balanced" },
        PaddingConfig { k: 3, d: 6,  label: "Balanced" },
        PaddingConfig { k: 4, d: 5,  label: "Balanced" },
        PaddingConfig { k: 5, d: 4,  label: "Balanced" },
        // Tier 3: Deep
        PaddingConfig { k: 2, d: 14, label: "Deep" },
        PaddingConfig { k: 3, d: 9,  label: "Deep" },
        PaddingConfig { k: 4, d: 7,  label: "Deep" },
        PaddingConfig { k: 5, d: 6,  label: "Deep" },
        // Tier 4: Maximal depth
        PaddingConfig { k: 2, d: 20, label: "Maximal" },
        PaddingConfig { k: 3, d: 13, label: "Maximal" },
        PaddingConfig { k: 4, d: 10, label: "Maximal" },
        PaddingConfig { k: 5, d: 9,  label: "Maximal" },
    ];

    const N_INPUT: usize = 1_048_577; // 2^20 + 1

    let is_global = cfg!(feature = "global_padding");
    let padding_mode = if is_global { "global" } else { "iterative" };
    const MAX_GENS: usize = 2_097_152;

    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(MAX_GENS, 1);

    let mut rng = rand::thread_rng();
    let g = pc_gens.B;
    let f = pc_gens.F;
    let g_table = RistrettoBasepointTable::create(&g);
    let f_table = RistrettoBasepointTable::create(&f);

    let c1_raw: Vec<RistrettoPoint> = (0..N_INPUT)
        .map(|_| RistrettoPoint::random(&mut rng))
        .collect();
    let c2_raw: Vec<RistrettoPoint> = (0..N_INPUT)
        .map(|_| RistrettoPoint::random(&mut rng))
        .collect();

    let mut indices: Vec<usize> = (0..N_INPUT).collect();
    indices.shuffle(&mut rng);
    let r_values: Vec<Scalar> = (0..N_INPUT).map(|_| Scalar::random(&mut rng)).collect();

    let mut c1_prime: Vec<RistrettoPoint> = indices.iter().map(|&i| c1_raw[i]).collect();
    let mut c2_prime: Vec<RistrettoPoint> = indices.iter().map(|&i| c2_raw[i]).collect();
    for (j, r) in r_values.iter().enumerate() {
        c1_prime[j] += &g_table * r;
        c2_prime[j] += &f_table * r;
    }

    for cfg_item in configs {
        let k = cfg_item.k;
        let d = cfg_item.d;

        let circuit_n = if is_global {
            let k_pow_d = pow_usize(k, d);
            let m = (N_INPUT + k_pow_d - 1) / k_pow_d;
            m * k_pow_d
        } else {
            let rem = N_INPUT % k;
            if rem == 0 {
                N_INPUT
            } else {
                N_INPUT + (k - rem)
            }
        };

        let k_pow_d = pow_usize(k, d);
        let m_display = (N_INPUT + k_pow_d - 1) / k_pow_d;

        let padding_display = if is_global {
            m_display * k_pow_d - N_INPUT
        } else {
            let mut n_j = N_INPUT;
            let mut total = 0usize;
            for _ in 0..d {
                let rem_j = n_j % k;
                let pad_j = if rem_j == 0 { 0 } else { k - rem_j };
                total += pad_j;
                n_j = (n_j + pad_j) / k;
            }
            total
        };

        let (c1_raw_b, c2_raw_b, c1p_b, c2p_b) = (
            batch_compress(&c1_raw),
            batch_compress(&c2_raw),
            batch_compress(&c1_prime),
            batch_compress(&c2_prime),
        );
        let input_padded = derive_challenge_e(
            &pc_gens, &bp_gens, &c1_raw_b, &c2_raw_b, &c1p_b, &c2p_b, N_INPUT, circuit_n,
        );

        let mut output_padded: Vec<Scalar> = indices.iter().map(|&i| input_padded[i]).collect();
        output_padded.resize(circuit_n, Scalar::ZERO);

        let r_prime: Scalar = {
            let s = (0..N_INPUT)
                .map(|j| r_values[j] * input_padded[indices[j]])
                .fold(Scalar::ZERO, |acc, x| acc + x);
            -s
        };

        {
            let mut t_prove = Transcript::new(b"MAYA-Shuffle-v1");
            let mut check_rng = rand::thread_rng();
            let (proof, out_commitment) = KShuffleGadget::prove(
                &pc_gens,
                &bp_gens,
                &mut t_prove,
                &input_padded,
                &output_padded,
                &c1_prime,
                &c2_prime,
                r_prime,
                k,
                d,
                &mut check_rng,
            )
            .expect("prove failed");
            let v_pc_gens = PedersenGens::default();
            let v_bp_gens = BulletproofGens::new(circuit_n, 1);
            let e_verify = &input_padded[..N_INPUT];
            let c_combined = vec![
                RistrettoPoint::vartime_multiscalar_mul(e_verify.iter(), c1_raw.iter()),
                RistrettoPoint::vartime_multiscalar_mul(e_verify.iter(), c2_raw.iter()),
            ];
            let mut t_verify_ts = Transcript::new(b"MAYA-Shuffle-v1");
            let result = KShuffleGadget::verify(
                &v_pc_gens,
                &v_bp_gens,
                &mut t_verify_ts,
                &proof,
                &input_padded,
                out_commitment,
                &c1_prime,
                &c2_prime,
                &c_combined,
            );
            assert!(
                result.is_ok(),
                "VERIFICATION FAILED: {}/k={}/d={}: {:?}",
                padding_mode, k, d, result.err()
            );
        }

        println!("  {} | k={} d={} m={} padding={}", cfg_item.label, k, d, m_display, padding_display);

        let _bench_label = format!(
            "padding/{}/{}/k={}/d={}/m={}",
            padding_mode, cfg_item.label, k, d, m_display
        );

        c.bench_function(&_bench_label, |b| {
            b.iter(|| {
                let mut t = Transcript::new(b"MAYA-Shuffle-v1");
                let mut bench_rng = rand::thread_rng();
                KShuffleGadget::prove(
                    &pc_gens, &bp_gens, &mut t,
                    &input_padded, &output_padded,
                    &c1_prime, &c2_prime,
                    r_prime, k, d,
                    &mut bench_rng,
                ).expect("bench prove failed");
            });
        });
    }

    // SUMMARY TABLE 
    let read_padding_mean_ms = |label: &str, k: usize, d: usize, m: usize| -> Option<f64> {
        let dir_name = format!("padding_{}_{}_k={}_d={}_m={}", padding_mode, label, k, d, m);
        let json_path = format!("target/criterion/{}/new/estimates.json", dir_name);
        let content = match std::fs::read_to_string(&json_path) {
            Ok(c) => c,
            Err(_) => {
                eprintln!("  [padding] Tried: {}", json_path);
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
        let ns_value: f64 = val_str[..val_end].trim().parse().ok()?;
        Some(ns_value / 1_000_000.0)
    };

    println!();
    println!("================================================================");
    println!("  Table 12: {} padding - proof generation time (ms)",
        if cfg!(feature = "global_padding") { "Global" } else { "Iterative" });
    println!("  N = 1,048,577");
    println!();
    println!("  Criterion reports the slope estimate on screen by default (linear");
    println!("  regression of time vs iteration count). The summary table");
    println!("  below uses the mean from target/criterion/*/new/estimates.json,");
    println!("  which is the arithmetic average per-iteration time.");
    println!("  Both differ by ~1%.");
    println!("================================================================");
    println!("  {:>12} {:>5} {:>5} {:>14}", "Tier", "k", "d", "Prover (ms)");
    println!("  {:>12} {:>5} {:>5} {:>14}", "------------", "-----", "-----", "--------------");
    for cfg_item in configs {
        let k = cfg_item.k;
        let d = cfg_item.d;
        let k_pow_d = pow_usize(k, d);
        let m = (N_INPUT + k_pow_d - 1) / k_pow_d;
        match read_padding_mean_ms(cfg_item.label, k, d, m) {
            Some(ms) => println!("  {:>12} {:>5} {:>5} {:>14.2}", cfg_item.label, k, d, ms),
            None     => println!("  {:>12} {:>5} {:>5} {:>14}", cfg_item.label, k, d, "—"),
        }
    }
    println!();
}

criterion_group! {
    name = padding_bench;
    config = Criterion::default()
        .sample_size(10)
        .measurement_time(std::time::Duration::from_secs(30));
    targets = padding_comparison_benchmark
}

//---Figure 3 - Folding Factor Sweet Spot---
fn folding_factor_benchmark(c: &mut Criterion) {
    if std::env::var("BENCH_FOLDING").is_err() {
        return;
    }
    let n_values: &[usize] = &[1_000, 10_000, 100_000, 1_000_000];
    let k_values: &[usize] = &[2, 3, 4, 5, 6, 8, 16];

    println!();
    println!("================================================================");
    println!("  Folding Factor Sweep (Figure 3)");
    println!("  N = {{10^3, 10^4, 10^5, 10^6}}, k = {{2, 3, 4, 5, 6, 8, 16}}");
    println!();
    println!("  Measuring proof generation time only, since this is where");
    println!("  the folding factor k has the greatest impact.");
    println!("================================================================");
    println!();

    let total_configs = n_values.len() * k_values.len();
    let mut config_index = 0usize;

    for &n_input in n_values {
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(n_input + 20, 1);

        let mut rng = rand::thread_rng();
        let g = pc_gens.B;
        let f = pc_gens.F;
        let g_table = RistrettoBasepointTable::create(&g);
        let f_table = RistrettoBasepointTable::create(&f);

        let c1_raw: Vec<RistrettoPoint> = (0..n_input)
            .map(|_| RistrettoPoint::random(&mut rng))
            .collect();
        let c2_raw: Vec<RistrettoPoint> = (0..n_input)
            .map(|_| RistrettoPoint::random(&mut rng))
            .collect();

        let mut indices: Vec<usize> = (0..n_input).collect();
        indices.shuffle(&mut rng);
        let r_values: Vec<Scalar> = (0..n_input).map(|_| Scalar::random(&mut rng)).collect();

        let mut c1_prime: Vec<RistrettoPoint> = indices.iter().map(|&i| c1_raw[i]).collect();
        let mut c2_prime: Vec<RistrettoPoint> = indices.iter().map(|&i| c2_raw[i]).collect();
        for (j, r) in r_values.iter().enumerate() {
            c1_prime[j] += &g_table * r;
            c2_prime[j] += &f_table * r;
        }

        for &k_fold in k_values {
            let rem = n_input % k_fold;
            let circuit_n = if rem == 0 {
                n_input
            } else {
                n_input + (k_fold - rem)
            };

            let mut n_j = circuit_n;
            let mut d = 0usize;
            while n_j > 1 {
                let rem_j = n_j % k_fold;
                let pad_j = if rem_j == 0 { 0 } else { k_fold - rem_j };
                n_j = (n_j + pad_j) / k_fold;
                d += 1;
            }
            let _final_m = n_j; 

            let (c1_raw_b, c2_raw_b, c1p_b, c2p_b) = (
                batch_compress(&c1_raw),
                batch_compress(&c2_raw),
                batch_compress(&c1_prime),
                batch_compress(&c2_prime),
            );
            let input_padded = derive_challenge_e(
                &pc_gens, &bp_gens, &c1_raw_b, &c2_raw_b, &c1p_b, &c2p_b, n_input, circuit_n,
            );

            let mut output_padded: Vec<Scalar> = indices.iter().map(|&i| input_padded[i]).collect();
            output_padded.resize(circuit_n, Scalar::ZERO);

            let r_prime: Scalar = {
                let s = (0..n_input)
                    .map(|j| r_values[j] * input_padded[indices[j]])
                    .fold(Scalar::ZERO, |acc, x| acc + x);
                -s
            };

            {
                let mut t_prove = Transcript::new(b"MAYA-Shuffle-v1");
                let mut check_rng = rand::thread_rng();
                let (proof, out_commitment) = KShuffleGadget::prove(
                    &pc_gens,
                    &bp_gens,
                    &mut t_prove,
                    &input_padded,
                    &output_padded,
                    &c1_prime,
                    &c2_prime,
                    r_prime,
                    k_fold,
                    d,
                    &mut check_rng,
                )
                .expect("folding bench: prove failed");
                let v_pc_gens = PedersenGens::default();
                let v_bp_gens = BulletproofGens::new(circuit_n, 1);
                let e_verify = &input_padded[..n_input];
                let c_combined = vec![
                    RistrettoPoint::vartime_multiscalar_mul(e_verify.iter(), c1_raw.iter()),
                    RistrettoPoint::vartime_multiscalar_mul(e_verify.iter(), c2_raw.iter()),
                ];
                let mut t_verify_ts = Transcript::new(b"MAYA-Shuffle-v1");
                let result = KShuffleGadget::verify(
                    &v_pc_gens,
                    &v_bp_gens,
                    &mut t_verify_ts,
                    &proof,
                    &input_padded,
                    out_commitment,
                    &c1_prime,
                    &c2_prime,
                    &c_combined,
                );
                assert!(
                    result.is_ok(),
                    "VERIFICATION FAILED: N={}/k={}/d={}: {:?}",
                    n_input, k_fold, d, result.err()
                );
            }

            config_index += 1;
            println!("  [{}/{}] N={}, k={}, d={}", config_index, total_configs, n_input, k_fold, d);
            let bench_label = format!("folding/N={}/k={}/d={}", n_input, k_fold, d);

            c.bench_function(&bench_label, |b| {
                b.iter(|| {
                    let mut t = Transcript::new(b"MAYA-Shuffle-v1");
                    let mut bench_rng = rand::thread_rng();
                    KShuffleGadget::prove(
                        &pc_gens,
                        &bp_gens,
                        &mut t,
                        &input_padded,
                        &output_padded,
                        &c1_prime,
                        &c2_prime,
                        r_prime,
                        k_fold,
                        d,
                        &mut bench_rng,
                    )
                    .expect("folding bench prove failed");
                });
            });
        }
    }

    println!();
    println!("================================================================");
    println!("  Figure 3: Proof generation time normalized to k=2");
    println!();
    println!("  Criterion reports the slope estimate on screen by default (linear");
    println!("  regression of time vs iteration count). The summary table");
    println!("  below uses the mean from target/criterion/*/new/estimates.json,");
    println!("  which is the arithmetic average per-iteration time.");
    println!("  Both differ by ~1%.");
    println!("================================================================");

    let read_folding_mean_ms = |n: usize, k: usize, d: usize| -> Option<f64> {
        let dir_name = format!("folding_N={}_k={}_d={}", n, k, d);
        let json_path = format!(
            "target/criterion/{}/new/estimates.json", dir_name
        );
        let content = std::fs::read_to_string(&json_path).ok()?;
        let mean_key = "\"mean\"";
        let pe_key = "\"point_estimate\":";
        let mean_pos = content.find(mean_key)?;
        let after_mean = &content[mean_pos..];
        let pe_pos = after_mean.find(pe_key)?;
        let val_start = pe_pos + pe_key.len();
        let val_str = &after_mean[val_start..];
        let val_end = val_str.find(|c: char| c == ',' || c == '}' || c == ' ')
            .unwrap_or(val_str.len());
        let ns_value: f64 = val_str[..val_end].trim().parse().ok()?;
        Some(ns_value / 1_000_000.0)
    };

    let compute_d = |n: usize, k: usize| -> usize {
        let rem = n % k;
        let mut n_j = if rem == 0 { n } else { n + (k - rem) };
        let mut d = 0usize;
        while n_j > 1 {
            let rem_j = n_j % k;
            let pad_j = if rem_j == 0 { 0 } else { k - rem_j };
            n_j = (n_j + pad_j) / k;
            d += 1;
        }
        d
    };

    print!("  {:>10}", "N");
    for &k in k_values { print!("  {:>7}", format!("k={}", k)); }
    println!();
    print!("  {:>10}", "----------");
    for _ in k_values { print!("  {:>7}", "-------"); }
    println!();

    for &n in n_values {
        print!("  {:>10}", n);
        let d_baseline = compute_d(n, 2);
        let baseline = read_folding_mean_ms(n, 2, d_baseline);

        for &k in k_values {
            let d_k = compute_d(n, k);
            match (read_folding_mean_ms(n, k, d_k), baseline) {
                (Some(t_k), Some(t_2)) if t_2 > 0.0 => {
                    print!("  {:>7.3}", t_k / t_2);
                }
                _ => {
                    print!("  {:>7}", "—");
                }
            }
        }
        println!();
    }
    println!();
}

criterion_group! {
    name = folding_bench;
    config = Criterion::default()
        .sample_size(10)
        .measurement_time(std::time::Duration::from_secs(30));
    targets = folding_factor_benchmark
}


//--- Multi-run averaging benchmark--- 
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
    println!("  Multi-run averaging benchmark");
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
            || PedersenGens::default(),
            || BulletproofGens::new(n_padded, 1),
        );
        #[cfg(not(feature = "parallel"))]
        let pc_gens = PedersenGens::default();
        #[cfg(not(feature = "parallel"))]
        let bp_gens = BulletproofGens::new(n_padded, 1);

        let g = pc_gens.B;
        let f = pc_gens.F;

        let g_table = RistrettoBasepointTable::create(&g);
        let f_table = RistrettoBasepointTable::create(&f);

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
        let c1_raw: Vec<RistrettoPoint> = (0..n_input).map(|_| RistrettoPoint::random(&mut rng)).collect();
        let c2_raw: Vec<RistrettoPoint> = (0..n_input).map(|_| RistrettoPoint::random(&mut rng)).collect();
        let c1_bytes = batch_compress(&c1_raw);
        let c2_bytes = batch_compress(&c2_raw);

        let mut prover_times: Vec<f64> = Vec::with_capacity(num_runs);
        let mut verifier_times: Vec<f64> = Vec::with_capacity(num_runs);

        for run in 0..num_runs {
            // Full prover pipeline
            let t_prover_start = Instant::now();

            // CRS generation
            #[cfg(feature = "parallel")]
            let (run_pc, run_bp) = rayon::join(
                || PedersenGens::default(),
                || BulletproofGens::new(n_padded, 1),
            );
            #[cfg(not(feature = "parallel"))]
            let run_pc = PedersenGens::default();
            #[cfg(not(feature = "parallel"))]
            let run_bp = BulletproofGens::new(n_padded, 1);

            // Fixed-base tables
            let run_g = run_pc.B;
            let run_f = run_pc.F;
            let run_g_table = RistrettoBasepointTable::create(&run_g);
            let run_f_table = RistrettoBasepointTable::create(&run_f);

            // Permutation
            let mut indices: Vec<usize> = (0..n_input).collect();
            indices.shuffle(&mut rng);

            // Rerandomization
            #[cfg(all(feature = "parallel", not(feature = "production")))]
            let r_values: Vec<Scalar> = (0..n_input).map(|j| deterministic_rand_scalar(j)).collect();
            #[cfg(not(feature = "parallel"))]
            let r_values: Vec<Scalar> = (0..n_input).map(|_| Scalar::random(&mut rng)).collect();

            #[cfg(feature = "parallel")]
            let (c1_prime, c2_prime) = {
                let mut c1p: Vec<RistrettoPoint> = indices.iter().map(|&i| c1_raw[i]).collect();
                let mut c2p: Vec<RistrettoPoint> = indices.iter().map(|&i| c2_raw[i]).collect();
                c1p.par_iter_mut()
                    .zip(c2p.par_iter_mut())
                    .zip(r_values.par_iter())
                    .for_each(|((a, b), r)| { *a += &run_g_table * r; *b += &run_f_table * r; });
                (c1p, c2p)
            };
            #[cfg(not(feature = "parallel"))]
            let (c1_prime, c2_prime) = {
                let mut c1p: Vec<RistrettoPoint> = indices.iter().map(|&i| c1_raw[i]).collect();
                let mut c2p: Vec<RistrettoPoint> = indices.iter().map(|&i| c2_raw[i]).collect();
                for (j, r) in r_values.iter().enumerate() {
                    c1p[j] += &run_g_table * r;
                    c2p[j] += &run_f_table * r;
                }
                (c1p, c2p)
            };

            // Challenge e derivation
            let c1p_bytes = batch_compress(&c1_prime);
            let c2p_bytes = batch_compress(&c2_prime);
            let input_padded = derive_challenge_e(
                &run_pc, &run_bp, &c1_bytes, &c2_bytes, &c1p_bytes, &c2p_bytes, n_input, circuit_n,
            );
            let mut output_padded: Vec<Scalar> = indices.iter().map(|&i| input_padded[i]).collect();
            output_padded.resize(circuit_n, Scalar::ZERO);
            let r_prime: Scalar = {
                let s = (0..n_input)
                    .map(|j| r_values[j] * input_padded[indices[j]])
                    .fold(Scalar::ZERO, |acc, x| acc + x);
                -s
            };

            // Proof generation
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

            // CRS regeneration
            #[cfg(feature = "parallel")]
            let (v_pc, v_bp) = rayon::join(
                || PedersenGens::default(),
                || BulletproofGens::new(n_padded, 1),
            );
            #[cfg(not(feature = "parallel"))]
            let v_pc = PedersenGens::default();
            #[cfg(not(feature = "parallel"))]
            let v_bp = BulletproofGens::new(n_padded, 1);

            // Challenge e re-derivation
            let input_padded_v = derive_challenge_e(
                &v_pc, &v_bp, &c1_bytes, &c2_bytes, &c1p_bytes, &c2p_bytes, n_input, circuit_n,
            );

            // RHS MSM
            let e_v = &input_padded_v[..n_input];
            #[cfg(feature = "parallel")]
            let c_combined = {
                let nt = rayon::current_num_threads();
                let cs = (n_input + nt - 1) / nt;
                let s0: RistrettoPoint = c1_raw.par_chunks(cs).zip(e_v.par_chunks(cs))
                    .map(|(pts, scs)| RistrettoPoint::vartime_multiscalar_mul(scs.iter(), pts.iter()))
                    .sum();
                let s1: RistrettoPoint = c2_raw.par_chunks(cs).zip(e_v.par_chunks(cs))
                    .map(|(pts, scs)| RistrettoPoint::vartime_multiscalar_mul(scs.iter(), pts.iter()))
                    .sum();
                vec![s0, s1]
            };
            #[cfg(not(feature = "parallel"))]
            let c_combined = vec![
                RistrettoPoint::vartime_multiscalar_mul(e_v.iter(), c1_raw.iter()),
                RistrettoPoint::vartime_multiscalar_mul(e_v.iter(), c2_raw.iter()),
            ];

            // Proof verification
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
// but Criterion still needs a valid group config
criterion_group! {
    name = full_avg_bench;
    config = Criterion::default().sample_size(10);
    targets = full_averaging_benchmark
}
criterion_main!(benches, padding_bench, folding_bench, full_avg_bench);
