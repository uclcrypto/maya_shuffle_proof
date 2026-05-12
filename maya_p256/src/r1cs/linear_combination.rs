//! Definition of linear combinations.

use ark_ff::PrimeField;
use std::iter::FromIterator;
use std::ops::{Add, Mul, Neg, Sub};

/// Represents a variable in a constraint system.
#[derive(Copy, Clone, Debug)]
pub enum Variable {
    Committed(usize),
    MultiplierLeft(usize),
    MultiplierRight(usize),
    MultiplierOutput(usize),
    One(),
}

/// Represents a linear combination of Variables.
/// Each term is (Variable, scalar_coefficient).
/// Generic over the scalar field F.
#[derive(Clone, Debug)]
pub struct LinearCombination<F: PrimeField> {
    pub(super) terms: Vec<(Variable, F)>,
}

impl<F: PrimeField> Default for LinearCombination<F> {
    fn default() -> Self {
        LinearCombination { terms: Vec::new() }
    }
}

impl<F: PrimeField> From<Variable> for LinearCombination<F> {
    fn from(v: Variable) -> LinearCombination<F> {
        LinearCombination {
            terms: vec![(v, F::one())],
        }
    }
}

impl<F: PrimeField> From<F> for LinearCombination<F> {
    fn from(s: F) -> LinearCombination<F> {
        LinearCombination {
            terms: vec![(Variable::One(), s)],
        }
    }
}

// Scalar arithmetic with variables

impl<F: PrimeField> Add<Variable> for LinearCombination<F> {
    type Output = LinearCombination<F>;
    fn add(mut self, other: Variable) -> Self::Output {
        self.terms.push((other, F::one()));
        self
    }
}

// LinearCombination arithmetic

impl<F: PrimeField> Add for LinearCombination<F> {
    type Output = Self;
    fn add(mut self, rhs: Self) -> Self::Output {
        self.terms.extend(rhs.terms.into_iter());
        self
    }
}

impl<F: PrimeField> Sub for LinearCombination<F> {
    type Output = Self;
    fn sub(mut self, rhs: Self) -> Self::Output {
        self.terms
            .extend(rhs.terms.into_iter().map(|(var, coeff)| (var, -coeff)));
        self
    }
}

impl<F: PrimeField> Sub<F> for LinearCombination<F> {
    type Output = Self;
    fn sub(self, rhs: F) -> Self::Output {
        self - LinearCombination::from(rhs)
    }
}

impl<F: PrimeField> Neg for LinearCombination<F> {
    type Output = Self;
    fn neg(mut self) -> Self::Output {
        for (_, s) in self.terms.iter_mut() {
            *s = -*s;
        }
        self
    }
}

impl<F: PrimeField> Mul<F> for LinearCombination<F> {
    type Output = Self;
    fn mul(mut self, other: F) -> Self::Output {
        for (_, s) in self.terms.iter_mut() {
            *s *= other;
        }
        self
    }
}

impl<F: PrimeField> Mul<LinearCombination<F>> for LinearCombination<F> {
    type Output = Self;
    fn mul(self, _rhs: Self) -> Self::Output {
        // Note: LC * LC is not directly supported in the constraint system;
        // this is only used for scalar * LC which is handled above.
        // For the shuffle gadget's `prev_lc * (-z)` pattern, we need this.
        unimplemented!("Cannot multiply two arbitrary LCs; use cs.multiply() instead")
    }
}

impl<F: PrimeField> FromIterator<(Variable, F)> for LinearCombination<F> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = (Variable, F)>,
    {
        LinearCombination {
            terms: iter.into_iter().collect(),
        }
    }
}
