extern crate curve25519_dalek;
extern crate maya_ristretto;
extern crate merlin;
extern crate rand;

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::VartimeMultiscalarMul;
use merlin::Transcript;
use rand::seq::SliceRandom;

use maya_ristretto::r1cs::R1CSProof;
use maya_ristretto::shuffle::{circuit_length, derive_challenge_e, num_fold_rounds, KShuffleGadget};
use maya_ristretto::{BulletproofGens, PedersenGens};

struct Shuffle {
    pc_gens: PedersenGens,
    bp_gens: BulletproofGens,
    c1_prime: Vec<RistrettoPoint>,
    c2_prime: Vec<RistrettoPoint>,
    c_combined: Vec<RistrettoPoint>,
    e: Vec<Scalar>,
    e_seed: [u8; 32],
    k_fold: usize,
    d: usize,
    proof: R1CSProof,
    commitment: CompressedRistretto,
}

fn bytes(points: &[RistrettoPoint]) -> Vec<u8> {
    points.iter().flat_map(|p| p.compress().to_bytes().to_vec()).collect()
}

fn shuffle(n: usize, k_fold: usize) -> Shuffle {
    let mut rng = rand::thread_rng();
    let circuit_n = circuit_length(n, k_fold);
    let d = num_fold_rounds(circuit_n, k_fold);
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(circuit_n, 1);

    let c1: Vec<RistrettoPoint> = (0..n).map(|_| RistrettoPoint::random(&mut rng)).collect();
    let c2: Vec<RistrettoPoint> = (0..n).map(|_| RistrettoPoint::random(&mut rng)).collect();
    let mut perm: Vec<usize> = (0..n).collect();
    perm.shuffle(&mut rng);
    let r: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
    let c1_prime: Vec<RistrettoPoint> = (0..n).map(|j| c1[perm[j]] + r[j] * pc_gens.B).collect();
    let c2_prime: Vec<RistrettoPoint> = (0..n).map(|j| c2[perm[j]] + r[j] * pc_gens.F).collect();

    let (e, e_seed) = derive_challenge_e(
        &pc_gens, &bp_gens, &bytes(&c1), &bytes(&c2), &bytes(&c1_prime), &bytes(&c2_prime),
        n, circuit_n,
    );
    let c_combined = vec![
        RistrettoPoint::vartime_multiscalar_mul(e[..n].iter(), c1.iter()),
        RistrettoPoint::vartime_multiscalar_mul(e[..n].iter(), c2.iter()),
    ];

    let mut output: Vec<Scalar> = perm.iter().map(|&i| e[i]).collect();
    output.resize(circuit_n, Scalar::ZERO);
    let r_prime = -(0..n).fold(Scalar::ZERO, |acc, j| acc + r[j] * e[perm[j]]);

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

fn verify(s: &Shuffle, proof: &R1CSProof, e_seed: &[u8; 32]) -> bool {
    let mut transcript = Transcript::new(b"MAYA-Shuffle-v1");
    KShuffleGadget::verify(
        &s.pc_gens, &s.bp_gens, &mut transcript, e_seed, proof, &s.e, s.commitment,
        &s.c1_prime, &s.c2_prime, &s.c_combined, s.k_fold, s.d,
    )
    .is_ok()
}



#[test]
fn honest_shuffle_verifies() {
    for &(n, k) in [(10usize, 4usize), (7, 3), (33, 2)].iter() {
        let s = shuffle(n, k);
        assert!(verify(&s, &s.proof, &s.e_seed), "n={} k={}", n, k);
        let parsed = R1CSProof::from_bytes(&s.proof.to_bytes()).unwrap();
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
        if let Ok(proof) = R1CSProof::from_bytes(&buf) {
            assert!(!verify(&s, &proof, &s.e_seed), "byte {} accepted", pos);
        }
    }
    let mut seed = s.e_seed;
    seed[0] ^= 1;
    assert!(!verify(&s, &s.proof, &seed));
}
