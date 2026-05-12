//! Utility functions for polynomial operations and scalar arithmetic.

#![allow(non_snake_case)]

use crate::inner_product_proof::inner_product;
use ark_ff::PrimeField;

/// Represents a degree-1 vector polynomial a + b * x
pub struct VecPoly1<F: PrimeField>(pub Vec<F>, pub Vec<F>);

/// Represents a degree-3 vector polynomial a + b*x + c*x^2 + d*x^3
#[cfg(feature = "yoloproofs")]
pub struct VecPoly3<F: PrimeField>(pub Vec<F>, pub Vec<F>, pub Vec<F>, pub Vec<F>);

/// Represents a degree-2 scalar polynomial a + b*x + c*x^2
pub struct Poly2<F: PrimeField>(pub F, pub F, pub F);

/// Represents a degree-6 scalar polynomial (without zeroth degree)
#[cfg(feature = "yoloproofs")]
pub struct Poly6<F: PrimeField> {
    pub t1: F,
    pub t2: F,
    pub t3: F,
    pub t4: F,
    pub t5: F,
    pub t6: F,
}

/// Iterator over powers of a scalar: 1, x, x^2, x^3, ...
pub struct ScalarExp<F: PrimeField> {
    x: F,
    next_exp_x: F,
}

impl<F: PrimeField> Iterator for ScalarExp<F> {
    type Item = F;

    fn next(&mut self) -> Option<F> {
        let exp_x = self.next_exp_x;
        self.next_exp_x *= self.x;
        Some(exp_x)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::max_value(), None)
    }
}

/// Return an iterator of the powers of `x`.
pub fn exp_iter<F: PrimeField>(x: F) -> ScalarExp<F> {
    let next_exp_x = F::one();
    ScalarExp { x, next_exp_x }
}

pub fn add_vec<F: PrimeField>(a: &[F], b: &[F]) -> Vec<F> {
    assert_eq!(
        a.len(),
        b.len(),
        "lengths of vectors don't match for vector addition"
    );
    a.iter().zip(b.iter()).map(|(ai, bi)| *ai + *bi).collect()
}

impl<F: PrimeField> VecPoly1<F> {
    pub fn zero(n: usize) -> Self {
        VecPoly1(vec![F::zero(); n], vec![F::zero(); n])
    }

    pub fn inner_product(&self, rhs: &VecPoly1<F>) -> Poly2<F> {
        let l = self;
        let r = rhs;

        let t0 = inner_product(&l.0, &r.0);
        let t2 = inner_product(&l.1, &r.1);

        let l0_plus_l1 = add_vec(&l.0, &l.1);
        let r0_plus_r1 = add_vec(&r.0, &r.1);

        let t1 = inner_product(&l0_plus_l1, &r0_plus_r1) - t0 - t2;

        Poly2(t0, t1, t2)
    }

    pub fn eval(&self, x: F) -> Vec<F> {
        let n = self.0.len();
        let mut out = vec![F::zero(); n];
        for i in 0..n {
            out[i] = self.0[i] + self.1[i] * x;
        }
        out
    }
}

#[cfg(feature = "yoloproofs")]
impl<F: PrimeField> VecPoly3<F> {
    pub fn zero(n: usize) -> Self {
        VecPoly3(
            vec![F::zero(); n],
            vec![F::zero(); n],
            vec![F::zero(); n],
            vec![F::zero(); n],
        )
    }

    pub fn special_inner_product(lhs: &Self, rhs: &Self) -> Poly6<F> {
        let t1 = inner_product(&lhs.1, &rhs.0);
        let t2 = inner_product(&lhs.1, &rhs.1) + inner_product(&lhs.2, &rhs.0);
        let t3 = inner_product(&lhs.2, &rhs.1) + inner_product(&lhs.3, &rhs.0);
        let t4 = inner_product(&lhs.1, &rhs.3) + inner_product(&lhs.3, &rhs.1);
        let t5 = inner_product(&lhs.2, &rhs.3);
        let t6 = inner_product(&lhs.3, &rhs.3);

        Poly6 {
            t1,
            t2,
            t3,
            t4,
            t5,
            t6,
        }
    }

    pub fn eval(&self, x: F) -> Vec<F> {
        let n = self.0.len();
        let mut out = vec![F::zero(); n];
        for i in 0..n {
            out[i] = self.0[i] + x * (self.1[i] + x * (self.2[i] + x * self.3[i]));
        }
        out
    }
}

impl<F: PrimeField> Poly2<F> {
    pub fn eval(&self, x: F) -> F {
        self.0 + x * (self.1 + x * self.2)
    }
}

#[cfg(feature = "yoloproofs")]
impl<F: PrimeField> Poly6<F> {
    pub fn eval(&self, x: F) -> F {
        x * (self.t1 + x * (self.t2 + x * (self.t3 + x * (self.t4 + x * (self.t5 + x * self.t6)))))
    }
}

/// Raises `x` to the power `n` using binary exponentiation.
pub fn scalar_exp_vartime<F: PrimeField>(x: &F, mut n: u64) -> F {
    let mut result = F::one();
    let mut aux = *x;
    while n > 0 {
        if n & 1 == 1 {
            result *= aux;
        }
        n >>= 1;
        aux = aux * aux;
    }
    result
}

/// Takes the sum of all the powers of `x`, up to `n`.
pub fn sum_of_powers<F: PrimeField>(x: &F, n: usize) -> F {
    if !n.is_power_of_two() {
        return sum_of_powers_slow(x, n);
    }
    if n == 0 || n == 1 {
        return F::from(n as u64);
    }
    let mut m = n;
    let mut result = F::one() + x;
    let mut factor = *x;
    while m > 2 {
        factor = factor * factor;
        result = result + factor * result;
        m /= 2;
    }
    result
}

fn sum_of_powers_slow<F: PrimeField>(x: &F, n: usize) -> F {
    exp_iter(*x).take(n).sum()
}

/// Given `data` with `len >= 32`, return the first 32 bytes.
pub fn read32(data: &[u8]) -> [u8; 32] {
    let mut buf32 = [0u8; 32];
    buf32[..].copy_from_slice(&data[..32]);
    buf32
}
