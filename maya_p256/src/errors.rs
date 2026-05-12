//! Errors related to proving and verifying proofs.

use thiserror::Error;

/// Represents an error in proof creation, verification, or parsing.
#[derive(Error, Clone, Debug, Eq, PartialEq)]
pub enum ProofError {
    #[error("n must be a power of k.")]
    FoldingError,
    #[error("Proof verification failed.")]
    VerificationError,
    #[error("Proof data could not be parsed.")]
    FormatError,
    #[error("Wrong number of blinding factors supplied.")]
    WrongNumBlindingFactors,
    #[error("Invalid bitsize, must have n = 8,16,32,64.")]
    InvalidBitsize,
    #[error("Invalid aggregation size, m must be a power of 2.")]
    InvalidAggregation,
    #[error("Invalid generators size, too few generators for proof")]
    InvalidGeneratorsLength,
    #[error("Internal error during proof creation: {0}")]
    ProvingError(MPCError),
}

impl From<MPCError> for ProofError {
    fn from(e: MPCError) -> ProofError {
        match e {
            MPCError::InvalidBitsize => ProofError::InvalidBitsize,
            MPCError::InvalidAggregation => ProofError::InvalidAggregation,
            MPCError::InvalidGeneratorsLength => ProofError::InvalidGeneratorsLength,
            _ => ProofError::ProvingError(e),
        }
    }
}

#[derive(Error, Clone, Debug, Eq, PartialEq)]
pub enum MPCError {
    #[error("Dealer gave a malicious challenge value.")]
    MaliciousDealer,
    #[error("Invalid bitsize, must have n = 8,16,32,64")]
    InvalidBitsize,
    #[error("Invalid aggregation size, m must be a power of 2")]
    InvalidAggregation,
    #[error("Invalid generators size, too few generators for proof")]
    InvalidGeneratorsLength,
    #[error("Wrong number of value commitments")]
    WrongNumBitCommitments,
    #[error("Wrong number of value commitments")]
    WrongNumPolyCommitments,
    #[error("Wrong number of proof shares")]
    WrongNumProofShares,
    #[error("Malformed proof shares from parties {bad_shares:?}")]
    MalformedProofShares { bad_shares: Vec<usize> },
}

/// Represents an error during the proving or verifying of a constraint system.
#[cfg(feature = "yoloproofs")]
#[derive(Error, Copy, Clone, Debug, Eq, PartialEq)]
pub enum R1CSError {
    #[error("Shuffle size must be more than 1.")]
    InputLengthError,
    #[error("Invalid generators size, too few generators for proof")]
    InvalidGeneratorsLength,
    #[error("R1CSProof did not verify correctly.")]
    VerificationError,
    #[error("Variable does not have a value assignment.")]
    MissingAssignment,
}
