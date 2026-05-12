#![allow(non_snake_case)]
#![allow(non_camel_case_types)]
#![allow(deprecated)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(dead_code)]
#![allow(non_local_definitions)]
#![allow(missing_docs)]
//#![feature(nll)]
//#![feature(external_doc)]
//#![feature(try_trait)]
//#![deny(missing_docs)]
//#![doc= include_str!("../README.md")]
#![doc(html_logo_url = "https://doc.dalek.rs/assets/dalek-logo-clear.png")]

extern crate byteorder;
extern crate core;
extern crate digest;
extern crate rand;
extern crate sha3;

extern crate curve25519_dalek;
extern crate merlin;
extern crate serde;
extern crate serde_derive;
extern crate subtle;
extern crate zeroize;

#[cfg(feature = "parallel")]
extern crate rayon;

#[macro_use]
extern crate failure;

#[cfg(test)]
extern crate bincode;

mod util;

#[doc= include_str!("../docs/notes-intro.md")]
mod notes {
    #[doc= include_str!("../docs/notes-ipp.md")]
    mod inner_product_proof {}
    #[doc= include_str!("../docs/notes-r1cs.md")]
    mod r1cs_proof {}
}

mod errors;
mod generators;
mod inner_product_proof;
pub mod transcript;

pub use errors::ProofError;
pub use generators::{BulletproofGens, BulletproofGensShare, PedersenGens};

pub mod range_proof_mpc {
    pub use errors::MPCError;
}

#[cfg(feature = "yoloproofs")]
pub mod r1cs;

