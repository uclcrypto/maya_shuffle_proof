//! Definition of the proof struct.

use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;

use inner_product_proof::prove_ecp;
use inner_product_proof::prove_ipa;

use errors::ProofError;
use serde::de::Visitor;
use serde::{self, Deserialize, Deserializer, Serialize, Serializer};
use std::convert::TryInto;

/// A proof of some statement specified by a
/// [`ConstraintSystem`](::r1cs::ConstraintSystem).
#[derive(Clone, Debug)]
#[allow(non_snake_case)]
pub struct R1CSProof {
    /// Commitment to the values of input wires
    pub(super) A_I: CompressedRistretto,
    /// Commitment to the values of output wires
    pub(super) A_O: CompressedRistretto,
    /// Commitment to the blinding factors
    pub(super) S: CompressedRistretto,

    /// Commitment to the \\(t_1\\) coefficient of \\( t(x) \\)
    pub(super) T_1: CompressedRistretto,
    /// Commitment to the \\(t_2\\) coefficient
    pub(super) T_2: CompressedRistretto,
    /// Commitment to the \\(t_3\\) coefficient of \\( t(x) \\)
    pub(super) T_3: CompressedRistretto,
    /// Commitment to the \\(t_4\\) coefficient of \\( t(x) \\)
    pub(super) T_4: CompressedRistretto,
    /// Commitment to the \\(t_5\\) coefficient of \\( t(x) \\)
    pub(super) T_5: CompressedRistretto,
    /// Commitment to the \\(t_6\\) coefficient of \\( t(x) \\)
    pub(super) T_6: CompressedRistretto,

    /// Evaluation of the polynomial \\(t(x)\\) at the challenge point \\(x\\)
    pub(super) t_x: Scalar,
    /// Blinding factor for the synthetic commitment to \\( t(x) \\)
    pub(super) t_x_blinding: Scalar,
    /// Blinding factor for the synthetic commitment to the inner-product arguments
    pub(super) e_blinding: Scalar,

    /// K-ary Bulletproof for main circuit
    pub(super) ipp_proof: prove_ipa,

    /// Shuffle consistency commitments
    pub(super) S_prime: CompressedRistretto,
    pub(super) T_1_prime: CompressedRistretto,
    pub(super) S1_prime: CompressedRistretto,
    pub(super) S2_prime: CompressedRistretto,

    /// Consistency check scalars
    pub(super) tc_x: Scalar,
    pub(super) tc_x_blinding: Scalar,
    pub(super) ec_blinding: Scalar,
    pub(super) t_cross: Scalar,
    pub(super) r_blinding: Scalar,

    /// Batched consistency proof
    pub(super) ecp_batched: prove_ecp,
}

impl R1CSProof {
    /// Serializes the proof into a byte array.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::new();

        buf.extend_from_slice(self.A_I.as_bytes());
        buf.extend_from_slice(self.A_O.as_bytes());
        buf.extend_from_slice(self.S.as_bytes());
        buf.extend_from_slice(self.T_1.as_bytes());
        buf.extend_from_slice(self.T_2.as_bytes());
        buf.extend_from_slice(self.T_3.as_bytes());
        buf.extend_from_slice(self.T_4.as_bytes());
        buf.extend_from_slice(self.T_5.as_bytes());
        buf.extend_from_slice(self.T_6.as_bytes());
        buf.extend_from_slice(self.S_prime.as_bytes());
        buf.extend_from_slice(self.T_1_prime.as_bytes());
        buf.extend_from_slice(self.S1_prime.as_bytes());
        buf.extend_from_slice(self.S2_prime.as_bytes());

        buf.extend_from_slice(self.t_x.as_bytes());
        buf.extend_from_slice(self.t_x_blinding.as_bytes());
        buf.extend_from_slice(self.e_blinding.as_bytes());
        buf.extend_from_slice(self.tc_x.as_bytes());
        buf.extend_from_slice(self.tc_x_blinding.as_bytes());
        buf.extend_from_slice(self.ec_blinding.as_bytes());
        buf.extend_from_slice(self.t_cross.as_bytes());
        buf.extend_from_slice(self.r_blinding.as_bytes());

        let ipp_proof_bytes = self.ipp_proof.to_bytes();
        let ecp_batched_bytes = self.ecp_batched.to_bytes();

        buf.extend_from_slice(&(ipp_proof_bytes.len() as u64).to_le_bytes());
        buf.extend_from_slice(&(ecp_batched_bytes.len() as u64).to_le_bytes());

        buf.extend_from_slice(ipp_proof_bytes.as_slice());
        buf.extend_from_slice(ecp_batched_bytes.as_slice());

        buf
    }

    /// Deserializes the proof from a byte slice.
    pub fn from_bytes(slice: &[u8]) -> Result<R1CSProof, ProofError> {
        let point_count = 13;
        let scalar_count = 8;
        let fixed_len = (point_count + scalar_count) * 32;
        let len_prefix_count = 2;
        let len_prefix_len = len_prefix_count * 8;

        if slice.len() < fixed_len + len_prefix_len {
            return Err(ProofError::FormatError);
        }

        let mut offset = 0;
        use util::read32;

        let mut read_point = |i: usize| -> CompressedRistretto {
            let pos = i * 32;
            CompressedRistretto(read32(&slice[pos..]))
        };

        let A_I = read_point(0);
        let A_O = read_point(1);
        let S = read_point(2);
        let T_1 = read_point(3);
        let T_2 = read_point(4);
        let T_3 = read_point(5);
        let T_4 = read_point(6);
        let T_5 = read_point(7);
        let T_6 = read_point(8);
        let S_prime = read_point(9);
        let T_1_prime = read_point(10);
        let S1_prime = read_point(11);
        let S2_prime = read_point(12);

        offset = point_count * 32;

        let mut read_scalar = |i: usize| -> Result<Scalar, ProofError> {
            let pos = offset + i * 32;
            Option::from(Scalar::from_canonical_bytes(read32(&slice[pos..])))
                .ok_or(ProofError::FormatError)
        };

        let t_x = read_scalar(0)?;
        let t_x_blinding = read_scalar(1)?;
        let e_blinding = read_scalar(2)?;
        let tc_x = read_scalar(3)?;
        let tc_x_blinding = read_scalar(4)?;
        let ec_blinding = read_scalar(5)?;
        let t_cross = read_scalar(6)?;
        let r_blinding = read_scalar(7)?;

        offset += scalar_count * 32;

        // Read proof lengths
        let mut read_len = |offset: &mut usize| -> Result<usize, ProofError> {
            if slice.len() < *offset + 8 {
                return Err(ProofError::FormatError);
            }
            let len_bytes: [u8; 8] = slice[*offset..*offset + 8]
                .try_into()
                .map_err(|_| ProofError::FormatError)?;
            *offset += 8;
            Ok(u64::from_le_bytes(len_bytes) as usize)
        };

        let ipp_proof_len = read_len(&mut offset)?;
        let ecp_batched_len = read_len(&mut offset)?;

        // Verify total length
        let total_expected_len = offset + ipp_proof_len + ecp_batched_len;

        if slice.len() != total_expected_len {
            return Err(ProofError::FormatError);
        }

        // Deserialize proofs
        let ipp_proof = prove_ipa::from_bytes(&slice[offset..offset + ipp_proof_len])?;
        offset += ipp_proof_len;

        let ecp_batched = prove_ecp::from_bytes(&slice[offset..offset + ecp_batched_len])?;

        Ok(R1CSProof {
            A_I,
            A_O,
            S,
            T_1,
            T_2,
            T_3,
            T_4,
            T_5,
            T_6,
            t_x,
            t_x_blinding,
            e_blinding,
            ipp_proof,
            S_prime,
            T_1_prime,
            tc_x,
            tc_x_blinding,
            ec_blinding,
            t_cross,
            S1_prime,
            S2_prime,
            r_blinding,
            ecp_batched,
        })
    }
}

impl Serialize for R1CSProof {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_bytes(&self.to_bytes()[..])
    }
}

impl<'de> Deserialize<'de> for R1CSProof {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct R1CSProofVisitor;

        impl<'de> Visitor<'de> for R1CSProofVisitor {
            type Value = R1CSProof;

            fn expecting(&self, formatter: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                formatter.write_str("a valid R1CSProof")
            }

            fn visit_bytes<E>(self, v: &[u8]) -> Result<R1CSProof, E>
            where
                E: serde::de::Error,
            {
                R1CSProof::from_bytes(v).map_err(serde::de::Error::custom)
            }
        }

        deserializer.deserialize_bytes(R1CSProofVisitor)
    }
}
