//! Definition of the constraint system trait.

use super::{LinearCombination, Variable};
use crate::errors::R1CSError;
use ark_ec::CurveGroup;
use ark_ff::PrimeField;

/// The interface for a constraint system, abstracting over the prover
/// and verifier's roles.
pub trait ConstraintSystem<G: CurveGroup> {
    type ScalarField: PrimeField;

    fn multiply(
        &mut self,
        left: LinearCombination<G::ScalarField>,
        right: LinearCombination<G::ScalarField>,
    ) -> (Variable, Variable, Variable);

    fn allocate<F>(&mut self, assign_fn: F) -> Result<(Variable, Variable, Variable), R1CSError>
    where
        F: FnOnce() -> Result<(G::ScalarField, G::ScalarField, G::ScalarField), R1CSError>;

    fn constrain(&mut self, lc: LinearCombination<G::ScalarField>);

    fn challenge_scalar(&mut self, label: &'static [u8]) -> G::ScalarField;
}
