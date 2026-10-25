use ark_ec::{CurveGroup, VariableBaseMSM};
use ark_ff::{UniformRand, Zero};
use ark_secp256r1::{Fr, Projective as G};
use merlin::Transcript;
use rand::seq::SliceRandom;

use maya_p256::r1cs::R1CSProof;
use maya_p256::shuffle::{circuit_length, derive_challenge_e, num_fold_rounds, KShuffleGadget};
use maya_p256::transcript::point_to_bytes;
use maya_p256::{BulletproofGens, PedersenGens};

struct Shuffle {
    pc_gens: PedersenGens<G>,
    bp_gens: BulletproofGens<G>,
    c1_prime: Vec<G>,
    c2_prime: Vec<G>,
    c_combined: Vec<G>,
    e: Vec<Fr>,
    e_seed: [u8; 32],
    k_fold: usize,
    d: usize,
    proof: R1CSProof<G>,
    commitment: Vec<u8>,
}

fn bytes(points: &[G]) -> Vec<u8> {
    points.iter().flat_map(point_to_bytes).collect()
}

fn msm(s: &[Fr], p: &[G]) -> G {
    G::msm(&G::normalize_batch(p), s).unwrap()
}

fn shuffle(n: usize, k_fold: usize) -> Shuffle {
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

    let (e, e_seed) = derive_challenge_e(
        &pc_gens, &bp_gens, &bytes(&c1), &bytes(&c2), &bytes(&c1_prime), &bytes(&c2_prime),
        n, circuit_n,
    );
    let c_combined = vec![msm(&e[..n], &c1), msm(&e[..n], &c2)];

    let mut output: Vec<Fr> = perm.iter().map(|&i| e[i]).collect();
    output.resize(circuit_n, Fr::zero());
    let r_prime = -(0..n).map(|j| r[j] * e[perm[j]]).sum::<Fr>();

    let mut transcript = Transcript::new(b"MAYA-Shuffle-v1");
    let (proof, commitment) = KShuffleGadget::prove(
        &pc_gens, &bp_gens, &mut transcript, &e_seed, &e, &output, &c1_prime, &c2_prime,
        r_prime, k_fold, d, &mut rng,
    )
    .expect("the prover accepts an honest shuffle");

    Shuffle {
        pc_gens, bp_gens, c1_prime, c2_prime, c_combined, e, e_seed, k_fold, d, proof, commitment,
    }
}

fn verify(s: &Shuffle, proof: &R1CSProof<G>, e_seed: &[u8; 32]) -> bool {
    let mut transcript = Transcript::new(b"MAYA-Shuffle-v1");
    KShuffleGadget::verify(
        &s.pc_gens, &s.bp_gens, &mut transcript, e_seed, proof, &s.e, s.commitment.clone(),
        &s.c1_prime, &s.c2_prime, &s.c_combined, s.k_fold, s.d,
    )
    .is_ok()
}

#[test]
fn honest_shuffle_verifies() {
    for &(n, k) in [(10usize, 4usize), (7, 3), (33, 2)].iter() {
        let s = shuffle(n, k);
        assert!(verify(&s, &s.proof, &s.e_seed), "n={} k={}", n, k);
        let parsed = R1CSProof::<G>::from_bytes(&s.proof.to_bytes()).unwrap();
        assert!(verify(&s, &parsed, &s.e_seed), "n={} k={} after serialization", n, k);
    }
}

#[test]
fn tampered_proof_and_wrong_statement_are_rejected() {
    let s = shuffle(10, 4);
    let good = s.proof.to_bytes();
    for pos in (0..good.len()).step_by(37) {
        let mut buf = good.clone();
        buf[pos] ^= 1;
        if let Ok(proof) = R1CSProof::<G>::from_bytes(&buf) {
            assert!(!verify(&s, &proof, &s.e_seed), "byte {} accepted", pos);
        }
    }
    let mut seed = s.e_seed;
    seed[0] ^= 1;
    assert!(!verify(&s, &s.proof, &seed));
}
