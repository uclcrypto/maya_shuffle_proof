//! Generator setup for Pedersen commitments and Bulletproofs.
//!
//! This module generates deterministic, independent group elements
//! for use as commitment bases, using a secure hash-to-group construction.
//!
//! # Security
//!
//! Generators are produced by a **try-and-increment hash-to-curve** method:
//! each candidate x-coordinate is derived from SHAKE256 output, and we check
//! whether `x^3 + ax + b` is a quadratic residue in the base field.  Because x
//! is determined by a hash, no one knows the discrete logarithm of the
//! resulting point relative to the curve's standard generator — the DLR
//! assumption required for soundness is preserved.

#![allow(non_snake_case)]

#[cfg(feature = "parallel")]
use rayon;

use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use byteorder::{ByteOrder, LittleEndian};
use digest::{ExtendableOutput, XofReader};
use sha3::Shake256;

use std::marker::PhantomData;

// HashToGroup trait
pub trait HashToGroup: CurveGroup {
    fn try_from_uniform_bytes(bytes: &[u8; 64]) -> Option<Self>;
}

impl HashToGroup for ark_secp256r1::Projective {
    fn try_from_uniform_bytes(bytes: &[u8; 64]) -> Option<Self> {
        use ark_ec::{short_weierstrass::SWCurveConfig, AffineRepr};
        use ark_ff::Field;
        use ark_secp256r1::{Affine, Config, Fq};

        let x = Fq::from_le_bytes_mod_order(bytes);

        let x2 = x.square();
        let x3 = x2 * x;
        let rhs = x3 + Config::COEFF_A * x + Config::COEFF_B;

        let y = rhs.sqrt()?;

        let affine = Affine::new_unchecked(x, y);
        Some(affine.into_group())
    }
}

#[derive(Clone)]
/// Pedersen commitment generators
pub struct PedersenGens<G: CurveGroup> {
    /// ElGamal generator g 
    pub B: G,
    /// Pedersen blinding base h
    pub B_blinding: G,
    /// ElGamal public key base f 
    pub F: G,
}

impl<G: CurveGroup> PedersenGens<G> {
    /// Creates a Pedersen commitment: value * B + blinding * B_blinding
    pub fn commit(&self, value: G::ScalarField, blinding: G::ScalarField) -> G {
        let bases = [self.B.into_affine(), self.B_blinding.into_affine()];
        let scalars = [value, blinding];
        G::msm(&bases, &scalars).expect("MSM in commit")
    }
}

impl<G: CurveGroup + HashToGroup> Default for PedersenGens<G> {
    fn default() -> Self {
       let mut chain = GeneratorsChain::<G>::new(b"PedersenGens");
        let B = chain.next().unwrap();
        let B_blinding = chain.next().unwrap();
        let F = chain.next().unwrap();
        PedersenGens { B, B_blinding, F }
    }
}

struct GeneratorsChain<G: CurveGroup> {
    reader: <Shake256 as ExtendableOutput>::Reader,
    _marker: PhantomData<G>,
}

impl<G: CurveGroup> GeneratorsChain<G> {
    fn new(label: &[u8]) -> Self {
        use digest::ExtendableOutput;
        let mut shake = Shake256::default();
        digest::Update::update(&mut shake, b"GeneratorsChain");
        digest::Update::update(&mut shake, label);
        GeneratorsChain {
            reader: shake.finalize_xof(),
            _marker: PhantomData,
        }
    }
}

impl<G: CurveGroup + HashToGroup> Iterator for GeneratorsChain<G> {
    type Item = G;

    fn next(&mut self) -> Option<G> {
        loop {
            let mut bytes = [0u8; 64];
            self.reader.read(&mut bytes);
            if let Some(pt) = G::try_from_uniform_bytes(&bytes) {
                return Some(pt);
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::max_value(), None)
    }
}

/// Bulletproof generators: vectors G and H of group elements.
#[derive(Clone)]
pub struct BulletproofGens<G: CurveGroup> {
    /// The maximum number of usable generators for each party.
    pub gens_capacity: usize,
    /// Number of values or parties
    pub party_capacity: usize,
    /// Precomputed G generators for each party.
    pub G_vec: Vec<Vec<G>>,
    /// Precomputed H generators for each party.
    pub H_vec: Vec<Vec<G>>,
}

#[cfg(feature = "parallel")]
impl<G: CurveGroup + HashToGroup + Send> BulletproofGens<G> {
   pub fn new(gens_capacity: usize, party_capacity: usize) -> Self {
        let (g_vec, h_vec) = rayon::join(
            || {
                (0..party_capacity)
                    .map(|i| {
                        let party_index = i as u32;
                        let mut label = [b'G', 0, 0, 0, 0];
                        LittleEndian::write_u32(&mut label[1..5], party_index);
                        GeneratorsChain::<G>::new(&label)
                            .take(gens_capacity)
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>()
            },
            || {
                (0..party_capacity)
                    .map(|i| {
                        let party_index = i as u32;
                        let mut label = [b'H', 0, 0, 0, 0];
                        LittleEndian::write_u32(&mut label[1..5], party_index);
                        GeneratorsChain::<G>::new(&label)
                            .take(gens_capacity)
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>()
            },
        );
        BulletproofGens {
            gens_capacity,
            party_capacity,
            G_vec: g_vec,
            H_vec: h_vec,
        }
    }
}

#[cfg(not(feature = "parallel"))]
impl<G: CurveGroup + HashToGroup> BulletproofGens<G> {
    pub fn new(gens_capacity: usize, party_capacity: usize) -> Self {
        BulletproofGens {
            gens_capacity,
            party_capacity,
            G_vec: (0..party_capacity)
                .map(|i| {
                    let party_index = i as u32;
                    let mut label = [b'G', 0, 0, 0, 0];
                    LittleEndian::write_u32(&mut label[1..5], party_index);
                    GeneratorsChain::<G>::new(&label)
                        .take(gens_capacity)
                        .collect::<Vec<_>>()
                })
                .collect(),
            H_vec: (0..party_capacity)
                .map(|i| {
                    let party_index = i as u32;
                    let mut label = [b'H', 0, 0, 0, 0];
                    LittleEndian::write_u32(&mut label[1..5], party_index);
                    GeneratorsChain::<G>::new(&label)
                        .take(gens_capacity)
                        .collect::<Vec<_>>()
                })
                .collect(),
        }
    }
}

impl<G: CurveGroup> BulletproofGens<G> {
    /// Returns j-th share of generators.
    pub fn share(&self, j: usize) -> BulletproofGensShare<'_, G> {
        BulletproofGensShare {
            gens: self,
            share: j,
        }
    }

    pub fn G(&self, n: usize, m: usize) -> impl Iterator<Item = &G> {
        AggregatedGensIter {
            array: &self.G_vec,
            n,
            m,
            party_idx: 0,
            gen_idx: 0,
        }
    }

    pub fn H(&self, n: usize, m: usize) -> impl Iterator<Item = &G> {
        AggregatedGensIter {
            array: &self.H_vec,
            n,
            m,
            party_idx: 0,
            gen_idx: 0,
        }
    }
}

struct AggregatedGensIter<'a, G: CurveGroup> {
    array: &'a Vec<Vec<G>>,
    n: usize,
    m: usize,
    party_idx: usize,
    gen_idx: usize,
}

impl<'a, G: CurveGroup> Iterator for AggregatedGensIter<'a, G> {
    type Item = &'a G;

    fn next(&mut self) -> Option<Self::Item> {
        if self.gen_idx >= self.n {
            self.gen_idx = 0;
            self.party_idx += 1;
        }
        if self.party_idx >= self.m {
            None
        } else {
            let cur_gen = self.gen_idx;
            self.gen_idx += 1;
            Some(&self.array[self.party_idx][cur_gen])
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.n * self.m;
        (size, Some(size))
    }
}

/// A view of the generators for a specific party.
#[derive(Copy, Clone)]
pub struct BulletproofGensShare<'a, G: CurveGroup> {
    gens: &'a BulletproofGens<G>,
    share: usize,
}

impl<'a, G: CurveGroup> BulletproofGensShare<'a, G> {
    pub fn G(&self, n: usize) -> impl Iterator<Item = &'a G> {
        self.gens.G_vec[self.share].iter().take(n)
    }

    pub fn H(&self, n: usize) -> impl Iterator<Item = &'a G> {
        self.gens.H_vec[self.share].iter().take(n)
    }
}
