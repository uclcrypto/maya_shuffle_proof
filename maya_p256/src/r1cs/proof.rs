//! Definition of the proof struct.

use ark_ec::CurveGroup;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use serde::de::Visitor;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::errors::ProofError;
use crate::inner_product_proof::prove_ecp;
use crate::inner_product_proof::prove_ipa;

/// A proof of some statement specified by a ConstraintSystem.
#[derive(Clone, Debug)]
#[allow(non_snake_case)]
pub struct R1CSProof<G: CurveGroup> {
    pub(super) A_I: Vec<u8>,
    pub(super) A_O: Vec<u8>,
    pub(super) S: Vec<u8>,

    pub(super) T_1: Vec<u8>,
    pub(super) T_2: Vec<u8>,
    pub(super) T_3: Vec<u8>,
    pub(super) T_4: Vec<u8>,
    pub(super) T_5: Vec<u8>,
    pub(super) T_6: Vec<u8>,

    pub(super) t_x: G::ScalarField,
    pub(super) t_x_blinding: G::ScalarField,
    pub(super) e_blinding: G::ScalarField,

    pub(super) ipp_proof: prove_ipa<G>,

    pub(super) S_prime: Vec<u8>,
    pub(super) T_1_prime: Vec<u8>,
    pub(super) S1_prime: Vec<u8>,
    pub(super) S2_prime: Vec<u8>,

    pub(super) tc_x: G::ScalarField,
    pub(super) tc_x_blinding: G::ScalarField,
    pub(super) ec_blinding: G::ScalarField,
    pub(super) t_cross: G::ScalarField,
    pub(super) r_blinding: G::ScalarField,

    pub(super) ecp_batched: prove_ecp<G>,
}

impl<G: CurveGroup> R1CSProof<G> {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::new();

        let write_bytes = |buf: &mut Vec<u8>, data: &[u8]| {
            buf.extend_from_slice(&(data.len() as u64).to_le_bytes());
            buf.extend_from_slice(data);
        };

        write_bytes(&mut buf, &self.A_I);
        write_bytes(&mut buf, &self.A_O);
        write_bytes(&mut buf, &self.S);
        write_bytes(&mut buf, &self.T_1);
        write_bytes(&mut buf, &self.T_2);
        write_bytes(&mut buf, &self.T_3);
        write_bytes(&mut buf, &self.T_4);
        write_bytes(&mut buf, &self.T_5);
        write_bytes(&mut buf, &self.T_6);
        write_bytes(&mut buf, &self.S_prime);
        write_bytes(&mut buf, &self.T_1_prime);
        write_bytes(&mut buf, &self.S1_prime);
        write_bytes(&mut buf, &self.S2_prime);

        let mut scalar_buf = Vec::new();
        for s in &[
            &self.t_x,
            &self.t_x_blinding,
            &self.e_blinding,
            &self.tc_x,
            &self.tc_x_blinding,
            &self.ec_blinding,
            &self.t_cross,
            &self.r_blinding,
        ] {
            scalar_buf.clear();
            s.serialize_compressed(&mut scalar_buf)
                .expect("scalar serialization");
            write_bytes(&mut buf, &scalar_buf);
        }

        let ipp_bytes = self.ipp_proof.to_bytes();
        let ecp_bytes = self.ecp_batched.to_bytes();
        buf.extend_from_slice(&(ipp_bytes.len() as u64).to_le_bytes());
        buf.extend_from_slice(&(ecp_bytes.len() as u64).to_le_bytes());
        buf.extend_from_slice(&ipp_bytes);
        buf.extend_from_slice(&ecp_bytes);

        buf
    }

    pub fn from_bytes(slice: &[u8]) -> Result<R1CSProof<G>, ProofError> {
        let mut pos = 0;

        let mut read_bytes = |slice: &[u8], pos: &mut usize| -> Result<Vec<u8>, ProofError> {
            if slice.len() < *pos + 8 {
                return Err(ProofError::FormatError);
            }
            let len = u64::from_le_bytes(
                slice[*pos..*pos + 8]
                    .try_into()
                    .map_err(|_| ProofError::FormatError)?,
            ) as usize;
            *pos += 8;
            if slice.len() < *pos + len {
                return Err(ProofError::FormatError);
            }
            let data = slice[*pos..*pos + len].to_vec();
            *pos += len;
            Ok(data)
        };

        let A_I = read_bytes(slice, &mut pos)?;
        let A_O = read_bytes(slice, &mut pos)?;
        let S = read_bytes(slice, &mut pos)?;
        let T_1 = read_bytes(slice, &mut pos)?;
        let T_2 = read_bytes(slice, &mut pos)?;
        let T_3 = read_bytes(slice, &mut pos)?;
        let T_4 = read_bytes(slice, &mut pos)?;
        let T_5 = read_bytes(slice, &mut pos)?;
        let T_6 = read_bytes(slice, &mut pos)?;
        let S_prime = read_bytes(slice, &mut pos)?;
        let T_1_prime = read_bytes(slice, &mut pos)?;
        let S1_prime = read_bytes(slice, &mut pos)?;
        let S2_prime = read_bytes(slice, &mut pos)?;

        let mut read_scalar = |slice: &[u8],
                               pos: &mut usize|
         -> Result<G::ScalarField, ProofError> {
            let data = {
                if slice.len() < *pos + 8 {
                    return Err(ProofError::FormatError);
                }
                let len = u64::from_le_bytes(
                    slice[*pos..*pos + 8]
                        .try_into()
                        .map_err(|_| ProofError::FormatError)?,
                ) as usize;
                *pos += 8;
                if slice.len() < *pos + len {
                    return Err(ProofError::FormatError);
                }
                let d = slice[*pos..*pos + len].to_vec();
                *pos += len;
                d
            };
            G::ScalarField::deserialize_compressed(&data[..]).map_err(|_| ProofError::FormatError)
        };

        let t_x = read_scalar(slice, &mut pos)?;
        let t_x_blinding = read_scalar(slice, &mut pos)?;
        let e_blinding = read_scalar(slice, &mut pos)?;
        let tc_x = read_scalar(slice, &mut pos)?;
        let tc_x_blinding = read_scalar(slice, &mut pos)?;
        let ec_blinding = read_scalar(slice, &mut pos)?;
        let t_cross = read_scalar(slice, &mut pos)?;
        let r_blinding = read_scalar(slice, &mut pos)?;

        if slice.len() < pos + 16 {
            return Err(ProofError::FormatError);
        }
        let ipp_len = u64::from_le_bytes(
            slice[pos..pos + 8]
                .try_into()
                .map_err(|_| ProofError::FormatError)?,
        ) as usize;
        pos += 8;
        let ecp_len = u64::from_le_bytes(
            slice[pos..pos + 8]
                .try_into()
                .map_err(|_| ProofError::FormatError)?,
        ) as usize;
        pos += 8;

        if slice.len() < pos + ipp_len + ecp_len {
            return Err(ProofError::FormatError);
        }

        let ipp_proof = prove_ipa::<G>::from_bytes(&slice[pos..pos + ipp_len])?;
        pos += ipp_len;
        let ecp_batched = prove_ecp::<G>::from_bytes(&slice[pos..pos + ecp_len])?;

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
            S1_prime,
            S2_prime,
            tc_x,
            tc_x_blinding,
            ec_blinding,
            t_cross,
            r_blinding,
            ecp_batched,
        })
    }
}

impl<G: CurveGroup> Serialize for R1CSProof<G> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_bytes(&self.to_bytes())
    }
}

impl<'de, G: CurveGroup> Deserialize<'de> for R1CSProof<G> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct R1CSProofVisitor<G>(std::marker::PhantomData<G>);

        impl<'de, G: CurveGroup> Visitor<'de> for R1CSProofVisitor<G> {
            type Value = R1CSProof<G>;

            fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                formatter.write_str("a valid R1CSProof")
            }

            fn visit_bytes<E>(self, v: &[u8]) -> Result<R1CSProof<G>, E>
            where
                E: serde::de::Error,
            {
                R1CSProof::<G>::from_bytes(v).map_err(serde::de::Error::custom)
            }
        }

        deserializer.deserialize_bytes(R1CSProofVisitor(std::marker::PhantomData))
    }
}
