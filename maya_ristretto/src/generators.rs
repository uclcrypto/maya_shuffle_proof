
#![allow(non_snake_case)]
#![deny(missing_docs)]

use curve25519_dalek::constants::RISTRETTO_BASEPOINT_COMPRESSED;
use curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::MultiscalarMul;

use digest::{Digest, ExtendableOutput, Update, XofReader};
use sha3::{Sha3_512, Shake256};

#[derive(Copy, Clone)]
/// Pedersen commitment generators
pub struct PedersenGens {
    /// ElGamal generator g 
    pub B: RistrettoPoint,
    /// Pedersen blinding base h
    pub B_blinding: RistrettoPoint,
    /// ElGamal public key base f 
    pub F: RistrettoPoint,
}

impl PedersenGens {
    /// Creates a Pedersen commitment using the value scalar and a blinding factor.
    pub fn commit(&self, value: Scalar, blinding: Scalar) -> RistrettoPoint {
        RistrettoPoint::multiscalar_mul(&[value, blinding], &[self.B, self.B_blinding])
    }
}

impl Default for PedersenGens {
    fn default() -> Self {
        PedersenGens {
            B: RISTRETTO_BASEPOINT_POINT,
            B_blinding: {
                let hash: [u8; 64] =
                    Sha3_512::digest(RISTRETTO_BASEPOINT_COMPRESSED.as_bytes()).into();
                RistrettoPoint::from_uniform_bytes(&hash)
            },
            F: {
                let mut hasher = Sha3_512::new();
                //hasher.update(b"PedersenGens_F");
                Digest::update(&mut hasher, b"PedersenGens_F");
                //hasher.update(RISTRETTO_BASEPOINT_COMPRESSED.as_bytes());
                Digest::update(&mut hasher, RISTRETTO_BASEPOINT_COMPRESSED.as_bytes());
                let hash: [u8; 64] = hasher.finalize().into();
                RistrettoPoint::from_uniform_bytes(&hash)
            },
        }
    }
}

/// The `GeneratorsChain` creates an arbitrary-long sequence of
/// orthogonal generators.  The sequence can be deterministically
/// produced starting with an arbitrary point.
struct GeneratorsChain {
    reader: Box<dyn XofReader>,
}

impl GeneratorsChain {
    fn new(label: &[u8]) -> Self {
        let mut shake = Shake256::default();
        shake.update(b"GeneratorsChain");
        shake.update(label);

        GeneratorsChain {
            reader: Box::new(shake.finalize_xof()),
        }
    }
}

impl Default for GeneratorsChain {
    fn default() -> Self {
        Self::new(&[])
    }
}

impl Iterator for GeneratorsChain {
    type Item = RistrettoPoint;

    fn next(&mut self) -> Option<Self::Item> {
        let mut uniform_bytes = [0u8; 64];
        self.reader.read(&mut uniform_bytes);

        Some(RistrettoPoint::from_uniform_bytes(&uniform_bytes))
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::max_value(), None)
    }
}

///
#[derive(Clone)]
pub struct BulletproofGens {
    /// The maximum number of usable generators for each party.
    pub gens_capacity: usize,
    /// Number of values or parties
    pub party_capacity: usize,
    /// Precomputed \\(\mathbf G\\) generators for each party.
    // NOTE: add pub G_vec so that we can pass the references in "prove_ipa"
    pub G_vec: Vec<Vec<RistrettoPoint>>,
    /// Precomputed \\(\mathbf H\\) generators for each party.
    pub H_vec: Vec<Vec<RistrettoPoint>>,
}

impl BulletproofGens {
    /// Create a new `BulletproofGens` object.
    ///
    /// # Inputs
    ///
    /// * `gens_capacity` is the number of generators to precompute
    ///    for each party.  
    /// * `party_capacity` is the maximum number of parties that can
    ///    produce an aggregated proof.
    pub fn new(gens_capacity: usize, party_capacity: usize) -> Self {
        use byteorder::{ByteOrder, LittleEndian};

        #[cfg(feature = "parallel")]
        {
            let (g_vec, h_vec) = rayon::join(
                || {
                    (0..party_capacity)
                        .map(|i| {
                            let party_index = i as u32;
                            let mut label = [b'G', 0, 0, 0, 0];
                            LittleEndian::write_u32(&mut label[1..5], party_index);
                            GeneratorsChain::new(&label)
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
                            GeneratorsChain::new(&label)
                                .take(gens_capacity)
                                .collect::<Vec<_>>()
                        })
                        .collect::<Vec<_>>()
                },
            );
            return BulletproofGens {
                gens_capacity,
                party_capacity,
                G_vec: g_vec,
                H_vec: h_vec,
            };
        }

        #[cfg(not(feature = "parallel"))]
        BulletproofGens {
            gens_capacity,
            party_capacity,
            G_vec: (0..party_capacity)
                .map(|i| {
                    let party_index = i as u32;
                    let mut label = [b'G', 0, 0, 0, 0];
                    LittleEndian::write_u32(&mut label[1..5], party_index);

                    GeneratorsChain::new(&label)
                        .take(gens_capacity)
                        .collect::<Vec<_>>()
                })
                .collect(),
            H_vec: (0..party_capacity)
                .map(|i| {
                    let party_index = i as u32;
                    let mut label = [b'H', 0, 0, 0, 0];
                    LittleEndian::write_u32(&mut label[1..5], party_index);

                    GeneratorsChain::new(&label)
                        .take(gens_capacity)
                        .collect::<Vec<_>>()
                })
                .collect(),
        }
    }

    /// Returns j-th share of generators, with an appropriate
    /// slice of vectors G and H for the j-th range proof.
    pub fn share(&self, j: usize) -> BulletproofGensShare<'_> {
        BulletproofGensShare {
            gens: &self,
            share: j,
        }
    }

    /// Return an iterator over the aggregation of the parties' G generators with given size `n`.
    pub(crate) fn G(&self, n: usize, m: usize) -> impl Iterator<Item = &RistrettoPoint> {
        AggregatedGensIter {
            n,
            m,
            array: &self.G_vec,
            party_idx: 0,
            gen_idx: 0,
        }
    }

    /// Return an iterator over the aggregation of the parties' H generators with given size `n`.
    pub(crate) fn H(&self, n: usize, m: usize) -> impl Iterator<Item = &RistrettoPoint> {
        AggregatedGensIter {
            n,
            m,
            array: &self.H_vec,
            party_idx: 0,
            gen_idx: 0,
        }
    }
}

struct AggregatedGensIter<'a> {
    array: &'a Vec<Vec<RistrettoPoint>>,
    n: usize,
    m: usize,
    party_idx: usize,
    gen_idx: usize,
}

impl<'a> Iterator for AggregatedGensIter<'a> {
    type Item = &'a RistrettoPoint;

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

/// Represents a view of the generators used by a specific party in an
/// aggregated proof.
///
/// The `BulletproofGens` struct represents generators for an aggregated
/// range proof `m` proofs of `n` bits each; the `BulletproofGensShare`
/// provides a view of the generators for one of the `m` parties' shares.
///
/// The `BulletproofGensShare` is produced by [`BulletproofGens::share()`].
#[derive(Copy, Clone)]
pub struct BulletproofGensShare<'a> {
    /// The parent object that this is a view into
    gens: &'a BulletproofGens,
    /// Which share we are
    share: usize,
}

impl<'a> BulletproofGensShare<'a> {
    /// Return an iterator over this party's G generators with given size `n`.
    pub(crate) fn G(&self, n: usize) -> impl Iterator<Item = &'a RistrettoPoint> {
        self.gens.G_vec[self.share].iter().take(n)
    }

    /// Return an iterator over this party's H generators with given size `n`.
    pub(crate) fn H(&self, n: usize) -> impl Iterator<Item = &'a RistrettoPoint> {
        self.gens.H_vec[self.share].iter().take(n)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn aggregated_gens_iter_matches_flat_map() {
        let gens = BulletproofGens::new(64, 8);

        let helper = |n: usize, m: usize| {
            let agg_G: Vec<RistrettoPoint> = gens.G(n, m).cloned().collect();
            let flat_G: Vec<RistrettoPoint> = gens
                .G_vec
                .iter()
                .take(m)
                .flat_map(move |G_j| G_j.iter().take(n))
                .cloned()
                .collect();

            let agg_H: Vec<RistrettoPoint> = gens.H(n, m).cloned().collect();
            let flat_H: Vec<RistrettoPoint> = gens
                .H_vec
                .iter()
                .take(m)
                .flat_map(move |H_j| H_j.iter().take(n))
                .cloned()
                .collect();

            assert_eq!(agg_G, flat_G);
            assert_eq!(agg_H, flat_H);
        };

        helper(64, 8);
        helper(64, 4);
        helper(64, 2);
        helper(64, 1);
        helper(32, 8);
        helper(32, 4);
        helper(32, 2);
        helper(32, 1);
        helper(16, 8);
        helper(16, 4);
        helper(16, 2);
        helper(16, 1);
    }
}
