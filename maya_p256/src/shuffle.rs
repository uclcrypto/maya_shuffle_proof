use ark_ff::{One, UniformRand, Zero};
use ark_secp256r1::{Fr, Projective as G};
use merlin::Transcript;
use rand::{CryptoRng, RngCore, SeedableRng};
use rand_chacha::ChaCha20Rng;
use std::time::Instant;

use crate::generators::{BulletproofGens, PedersenGens};
use crate::r1cs::{
    ConstraintSystem, LinearCombination, Prover, R1CSError, R1CSProof, Variable, Verifier,
};
use crate::transcript::{point_to_bytes, TranscriptProtocol};

/// Padded length of the circuit vectors 
pub fn circuit_length(n: usize, k: usize) -> usize {
    if k < 2 || n % k == 0 {
        n
    } else {
        n + (k - n % k)
    }
}

/// Number of folding rounds
pub fn num_fold_rounds(n: usize, k: usize) -> usize {
    if k < 2 {
        return 0;
    }
    let mut n_j = n;
    let mut d = 0;
    while n_j > 1 {
        let rem = n_j % k;
        let pad = if rem == 0 { 0 } else { k - rem };
        n_j = (n_j + pad) / k;
        d += 1;
    }
    d
}

// --- Shuffle Gadget ---
pub struct KShuffleGadget;

impl KShuffleGadget {
    fn fill_cs<CS: ConstraintSystem<G, ScalarField = Fr>>(
        cs: &mut CS,
        x: &[Variable],
        y: &[Fr],
        k_original: usize,
    ) {
        let z: Fr = cs.challenge_scalar(b"k-scalar shuffle challenge");
        let k = x.len();

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

    fn bind_statement(
        transcript: &mut Transcript,
        k: usize,
        e_seed: &[u8; 32],
        k_original: usize,
        k_fold: usize,
        num_rounds: usize,
    ) {
        let mut scalar_buf = Vec::new();
        ark_serialize::CanonicalSerialize::serialize_compressed(
            &Fr::from(k as u64),
            &mut scalar_buf,
        )
        .unwrap();
        transcript.append_message(b"dom-sep", b"ShuffleProof");
        transcript.append_message(b"k", &scalar_buf);
        transcript.append_message(b"statement", e_seed);
        transcript.append_message(b"n", &(k_original as u64).to_le_bytes());
        transcript.append_message(b"k_fold", &(k_fold as u64).to_le_bytes());
        transcript.append_message(b"d", &(num_rounds as u64).to_le_bytes());
    }

    /// Proves that `(c1_prime, c2_prime)` is a re-encryption and a permutation of the input ciphertexts
    pub fn prove(
        pc_gens: &PedersenGens<G>,
        bp_gens: &BulletproofGens<G>,
        transcript: &mut Transcript,
        e_seed: &[u8; 32],
        input: &[Fr],
        output: &[Fr],
        c1_prime: &[G],
        c2_prime: &[G],
        r_prime: Fr,
        k_fold: usize,
        num_rounds: usize,
        rng: &mut (impl RngCore + CryptoRng),
    ) -> Result<(R1CSProof<G>, Vec<u8>), R1CSError> {
        let k = input.len();
        let k_original = c1_prime.len();
        if k <= 1 {
            return Err(R1CSError::InputLengthError);
        }
        if output.len() != k || k_original == 0 || k_original > k || c2_prime.len() != k_original {
            return Err(R1CSError::FormatError);
        }

        Self::bind_statement(transcript, k, e_seed, k_original, k_fold, num_rounds);

        let mut prover = Prover::<G>::new(bp_gens, pc_gens, transcript);
        let v_blinding = Fr::rand(rng);
        let (output_commitment, output_vars) =
            prover.commit_vec(output, v_blinding, k_original)?;
        let mut cs = prover.finalize_inputs();
        Self::fill_cs(&mut cs, &output_vars, input, k_original);
        let proof = cs.prove(c1_prime, c2_prime, r_prime, k_fold, num_rounds)?;
        Ok((proof, output_commitment))
    }

    /// Verifies a shuffle proof
    pub fn verify(
        pc_gens: &PedersenGens<G>,
        bp_gens: &BulletproofGens<G>,
        transcript: &mut Transcript,
        e_seed: &[u8; 32],
        proof: &R1CSProof<G>,
        input: &[Fr],
        output_commitment: Vec<u8>,
        c1_prime: &[G],
        c2_prime: &[G],
        c_combined: &[G],
        k_fold: usize,
        num_rounds: usize,
    ) -> Result<(), R1CSError> {
        let k = input.len();
        let k_original = c1_prime.len();
        if k <= 1 {
            return Err(R1CSError::InputLengthError);
        }
        if k_original == 0 || k_original > k || c2_prime.len() != k_original {
            return Err(R1CSError::FormatError);
        }

        Self::bind_statement(transcript, k, e_seed, k_original, k_fold, num_rounds);

        let mut verifier = Verifier::<G>::new(bp_gens, pc_gens, transcript);
        let output_vars = verifier.commit_vec(output_commitment, k);
        let mut cs = verifier.finalize_inputs();
        Self::fill_cs(&mut cs, &output_vars, input, k_original);
        cs.verify(proof, c1_prime, c2_prime, c_combined, k_fold, num_rounds)
    }
}

// Derive the challenge vector e deterministically from public parameters via
// Fiat-Shamir: e = PRG(Hash(pk, ck, C, C'))
pub fn derive_challenge_e(
    pc_gens: &PedersenGens<G>,
    bp_gens: &BulletproofGens<G>,
    c1_bytes: &[u8],
    c2_bytes: &[u8],
    c1p_bytes: &[u8],
    c2p_bytes: &[u8],
    n_original: usize,
    n_padded: usize,
) -> (Vec<Fr>, [u8; 32]) {
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

    (e, seed)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::inner_product_proof::fold_pad_counts;
    use ark_ec::{CurveGroup, VariableBaseMSM};
    use rand::seq::SliceRandom;

    struct Instance {
        pc_gens: PedersenGens<G>,
        bp_gens: BulletproofGens<G>,
        c1_prime: Vec<G>,
        c2_prime: Vec<G>,
        e: Vec<Fr>,
        e_seed: [u8; 32],
        c_combined: Vec<G>,
        k_fold: usize,
        d: usize,
        proof: R1CSProof<G>,
        output_commitment: Vec<u8>,
    }

    fn compress_all(points: &[G]) -> Vec<u8> {
        points.iter().flat_map(|p| point_to_bytes(p)).collect()
    }

    fn msm(s: &[Fr], p: &[G]) -> G {
        G::msm(&G::normalize_batch(p), s).unwrap()
    }

    fn challenge(
        pc_gens: &PedersenGens<G>,
        bp_gens: &BulletproofGens<G>,
        c1: &[G],
        c2: &[G],
        c1_prime: &[G],
        c2_prime: &[G],
        n_padded: usize,
    ) -> (Vec<Fr>, [u8; 32], Vec<G>) {
        let (e, seed) = derive_challenge_e(
            pc_gens,
            bp_gens,
            &compress_all(c1),
            &compress_all(c2),
            &compress_all(c1_prime),
            &compress_all(c2_prime),
            c1.len(),
            n_padded,
        );
        let n = c1.len();
        let c_combined = vec![msm(&e[..n], c1), msm(&e[..n], c2)];
        (e, seed, c_combined)
    }

    fn honest_instance(n: usize, k_fold: usize) -> Instance {
        let mut rng = rand::thread_rng();
        let circuit_n = circuit_length(n, k_fold);
        let d = num_fold_rounds(circuit_n, k_fold);
        let pc_gens = PedersenGens::<G>::default();
        let bp_gens = BulletproofGens::<G>::new(circuit_n, 1);
        let c1: Vec<G> = (0..n).map(|_| G::rand(&mut rng)).collect();
        let c2: Vec<G> = (0..n).map(|_| G::rand(&mut rng)).collect();
        let mut perm: Vec<usize> = (0..n).collect();
        perm.shuffle(&mut rng);
        let r: Vec<Fr> = (0..n).map(|_| Fr::rand(&mut rng)).collect();
        let c1_prime: Vec<G> = (0..n).map(|j| c1[perm[j]] + pc_gens.B * r[j]).collect();
        let c2_prime: Vec<G> = (0..n).map(|j| c2[perm[j]] + pc_gens.F * r[j]).collect();
        let (e, e_seed, c_combined) =
            challenge(&pc_gens, &bp_gens, &c1, &c2, &c1_prime, &c2_prime, circuit_n);
        let mut output: Vec<Fr> = perm.iter().map(|&i| e[i]).collect();
        output.resize(circuit_n, Fr::zero());
        let r_prime = -(0..n).map(|j| r[j] * e[perm[j]]).sum::<Fr>();
        let mut transcript = Transcript::new(b"MAYA-Shuffle-test");
        let (proof, output_commitment) = KShuffleGadget::prove(
            &pc_gens, &bp_gens, &mut transcript, &e_seed, &e, &output, &c1_prime, &c2_prime,
            r_prime, k_fold, d, &mut rng,
        )
        .unwrap();
        Instance {
            pc_gens, bp_gens, c1_prime, c2_prime, e, e_seed,
            c_combined, k_fold, d, proof, output_commitment,
        }
    }

    fn verify_with(
        inst: &Instance,
        proof: &R1CSProof<G>,
        e: &[Fr],
        e_seed: &[u8; 32],
        c1_prime: &[G],
        c2_prime: &[G],
        c_combined: &[G],
        k_fold: usize,
        d: usize,
    ) -> Result<(), R1CSError> {
        let mut transcript = Transcript::new(b"MAYA-Shuffle-test");
        KShuffleGadget::verify(
            &inst.pc_gens, &inst.bp_gens, &mut transcript, e_seed, proof, e,
            inst.output_commitment.clone(), c1_prime, c2_prime, c_combined, k_fold, d,
        )
    }

    fn verify(inst: &Instance, proof: &R1CSProof<G>) -> Result<(), R1CSError> {
        verify_with(
            inst, proof, &inst.e, &inst.e_seed, &inst.c1_prime, &inst.c2_prime,
            &inst.c_combined, inst.k_fold, inst.d,
        )
    }

    #[test]
    fn honest_shuffles_verify_for_lengths_that_are_not_powers_of_k() {
        let mut padded_configs = 0;
        for &(n, k) in &[(2, 2), (5, 4), (7, 3), (10, 4), (33, 4)] {
            let inst = honest_instance(n, k);
            //Counting configurations with padding
            if fold_pad_counts(circuit_length(n, k), k, inst.d).iter().any(|&p| p > 0) {
                padded_configs += 1;
            }
            assert_eq!(verify(&inst, &inst.proof), Ok(()), "n={} k={}", n, k);
        }
        assert!(padded_configs >= 3);
    }

   #[test]
    fn tampered_proofs_are_rejected() {
        let inst = honest_instance(5, 4);
        let bytes = inst.proof.to_bytes();
        let mut positions: Vec<usize> = (0..bytes.len()).step_by(29).collect();
        positions.push(bytes.len() - 1);
        for &pos in &positions {
            let mut tampered = bytes.clone();
            tampered[pos] ^= 0x01;
            if let Ok(proof) = R1CSProof::<G>::from_bytes(&tampered) {
                assert!(verify(&inst, &proof).is_err(), "tampered byte {} accepted", pos);
            }
        }
        assert!(R1CSProof::<G>::from_bytes(&bytes[..bytes.len() - 1]).is_err());
        let mut extended = bytes.clone();
        extended.push(0);
        assert!(R1CSProof::<G>::from_bytes(&extended).is_err());
    }

    #[test]
    fn malformed_proof_bytes_are_rejected() {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        for _ in 0..2000 {
            let len = rng.gen_range(0..600);
            let buf: Vec<u8> = (0..len).map(|_| rng.gen::<u8>()).collect();
            assert!(R1CSProof::<G>::from_bytes(&buf).is_err());
        }

        let inst = honest_instance(10, 4);
        let good = inst.proof.to_bytes();
        for pos in (0..good.len() - 8).step_by(8) {
            for &v in [u64::MAX, 1u64 << 32, 1u64 << 40, 1u64 << 60].iter() {
                let mut buf = good.clone();
                buf[pos..pos + 8].copy_from_slice(&v.to_le_bytes());
                if buf == good {
                    continue;
                }
                if let Ok(proof) = R1CSProof::<G>::from_bytes(&buf) {
                    assert!(verify(&inst, &proof).is_err(), "forged length at {} accepted", pos);
                }
            }
        }
    }

   #[test]
    fn folding_parameters_are_pinned() {
        let inst = honest_instance(10, 4);
        let wrong = [(inst.k_fold, inst.d + 1), (inst.k_fold, inst.d - 1), (2, inst.d), (8, inst.d)];
        for &(k, d) in &wrong {
            assert_eq!(
                verify_with(
                    &inst, &inst.proof, &inst.e, &inst.e_seed, &inst.c1_prime, &inst.c2_prime,
                    &inst.c_combined, k, d,
                ),
                Err(R1CSError::FormatError),
                "k={} d={}",
                k,
                d
            );
        }
    }


    // The seed of e is absorbed into the main transcript, so the challenges
    // depend on the statement and a proof does not carry over to another one.
    #[test]
    fn proof_is_bound_to_the_statement() {
        let inst = honest_instance(10, 4);
        for &byte in [0usize, 7, 31].iter() {
            let mut seed = inst.e_seed;
            seed[byte] ^= 1;
            assert!(verify_with(
                &inst, &inst.proof, &inst.e, &seed, &inst.c1_prime, &inst.c2_prime,
                &inst.c_combined, inst.k_fold, inst.d,
            )
            .is_err());
        }
    }

    //Binding the statement and the folding parameters to the main transcript.
    #[test]
    #[ignore]
    fn statement_binding_cost() {
        let seed = [7u8; 32];
        let reps = 20_000;
        let start = Instant::now();
        for _ in 0..reps {
            let mut t = Transcript::new(b"MAYA-Shuffle-v1");
            KShuffleGadget::bind_statement(&mut t, 1 << 20, &seed, 1_000_000, 4, 10);
        }
        println!();
        println!("statement binding: {:.3} us per proof",
                 start.elapsed().as_secs_f64() * 1e6 / reps as f64);
    }

    #[test]
    #[ignore]
    fn blinding_rng_cost() {
        use rand::SeedableRng;
        let draws = 2_000_000;
        let mut acc = Fr::zero();

        let mut before = rand::rngs::StdRng::from_seed([1u8; 32]);
        let start = Instant::now();
        for _ in 0..draws {
            acc += Fr::rand(&mut before);
        }
        let ms_before = start.elapsed().as_secs_f64() * 1e3;

        let mut after = rand_chacha::ChaCha20Rng::from_seed([1u8; 32]);
        let start = Instant::now();
        for _ in 0..draws {
            acc += Fr::rand(&mut after);
        }
        let ms_after = start.elapsed().as_secs_f64() * 1e3;

        assert_ne!(acc, Fr::zero());
        println!();
        println!("{} blinding scalars: before {:.1} ms, after {:.1} ms, delta {:.1} ms",
                 draws, ms_before, ms_after, ms_after - ms_before);
    }

    #[test]
    fn malformed_statements_are_rejected() {
        let inst = honest_instance(5, 4);
        let mut longer = inst.c1_prime.clone();
        longer.extend(inst.c1_prime.iter().cloned());
        assert!(verify_with(
            &inst, &inst.proof, &inst.e, &inst.e_seed, &longer, &longer, &inst.c_combined,
            inst.k_fold, inst.d,
        )
        .is_err());
        assert!(verify_with(
            &inst, &inst.proof, &inst.e, &inst.e_seed, &inst.c1_prime, &inst.c2_prime[1..],
            &inst.c_combined, inst.k_fold, inst.d,
        )
        .is_err());
        assert!(verify_with(
            &inst, &inst.proof, &inst.e, &inst.e_seed, &inst.c1_prime, &inst.c2_prime,
            &inst.c_combined[..1], inst.k_fold, inst.d,
        )
        .is_err());
        assert_eq!(
            verify_with(
                &inst, &inst.proof, &inst.e[..1], &inst.e_seed, &inst.c1_prime[..1],
                &inst.c2_prime[..1], &inst.c_combined, inst.k_fold, inst.d,
            ),
            Err(R1CSError::InputLengthError)
        );
        assert!(verify_with(
            &inst, &inst.proof, &inst.e, &inst.e_seed, &[], &[], &inst.c_combined, inst.k_fold,
            inst.d,
        )
        .is_err());

        let mut rng = rand::thread_rng();
        let mut transcript = Transcript::new(b"MAYA-Shuffle-test");
        let res = KShuffleGadget::prove(
            &inst.pc_gens, &inst.bp_gens, &mut transcript, &inst.e_seed, &inst.e,
            &inst.e[1..], &inst.c1_prime, &inst.c2_prime, Fr::zero(), inst.k_fold, inst.d,
            &mut rng,
        );
        assert!(res.is_err());
    }
}