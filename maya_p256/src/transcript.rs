//! Defines a `TranscriptProtocol` trait for using a Merlin transcript
//! with arkworks types.

use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_serialize::CanonicalSerialize;
use byteorder::{ByteOrder, LittleEndian};
use merlin::Transcript;

/// Extension trait for Merlin transcripts to work with arkworks types.
///
/// Instead of committing `CompressedRistretto` points, we commit
/// canonical serialized bytes of any arkworks group element.
pub trait TranscriptProtocol<G: CurveGroup> {
    /// Commit a domain separator for a length-`n` inner product proof.
    fn innerproduct_domain_sep(&mut self, n: u64);
    /// Commit a domain separator for a constraint system.
    fn r1cs_domain_sep(&mut self);
    /// Commit a 64-bit integer.
    fn commit_u64(&mut self, label: &'static [u8], n: u64);
    /// Commit a scalar with the given label.
    fn commit_scalar(&mut self, label: &'static [u8], scalar: &G::ScalarField);
    /// Commit a compressed point with the given label.
    fn commit_point(&mut self, label: &'static [u8], point: &[u8]);
    /// Compute a labeled challenge variable.
    fn challenge_scalar(&mut self, label: &'static [u8]) -> G::ScalarField;
}

fn le_u64(value: u64) -> [u8; 8] {
    let mut value_bytes = [0u8; 8];
    LittleEndian::write_u64(&mut value_bytes, value);
    value_bytes
}

impl<G: CurveGroup> TranscriptProtocol<G> for Transcript
where
    G::ScalarField: PrimeField,
{
    fn innerproduct_domain_sep(&mut self, n: u64) {
        self.append_message(b"dom-sep", b"ipp v1");
        self.append_message(b"n", &le_u64(n));
    }

    fn r1cs_domain_sep(&mut self) {
        self.append_message(b"dom-sep", b"r1cs v1");
    }

    fn commit_u64(&mut self, label: &'static [u8], n: u64) {
        self.append_message(label, &le_u64(n));
    }

    fn commit_scalar(&mut self, label: &'static [u8], scalar: &G::ScalarField) {
        let mut buf = Vec::new();
        scalar
            .serialize_compressed(&mut buf)
            .expect("scalar serialization");
        self.append_message(label, &buf);
    }

    fn commit_point(&mut self, label: &'static [u8], point_bytes: &[u8]) {
        self.append_message(label, point_bytes);
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> G::ScalarField {
        let mut buf = [0u8; 64];
        self.challenge_bytes(label, &mut buf);
        // Reduce the 512-bit value mod the field order
        G::ScalarField::from_le_bytes_mod_order(&buf)
    }
}

/// Helper: serialize a projective point to compressed bytes
pub fn point_to_bytes<G: CurveGroup>(point: &G) -> Vec<u8> {
    let affine = point.into_affine();
    let mut buf = Vec::new();
    affine
        .serialize_compressed(&mut buf)
        .expect("point serialization");
    buf
}
