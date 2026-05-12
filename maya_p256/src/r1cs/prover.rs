//! Prover implementation for the R1CS shuffle proof.

use ark_ec::CurveGroup;
use ark_ff::{Field, One, UniformRand, Zero};
use merlin::Transcript;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Instant;

static TIMING_PRINTED: AtomicBool = AtomicBool::new(false);

#[cfg(feature = "parallel")]
use rayon::prelude::*;

use super::{ConstraintSystem, LinearCombination, R1CSProof, Variable};
use crate::errors::R1CSError;
use crate::generators::{BulletproofGens, PedersenGens};
use crate::inner_product_proof::{inner_product, prove_ecp, prove_ipa};
use crate::transcript::{point_to_bytes, TranscriptProtocol};
use crate::util;

fn do_msm<G: CurveGroup>(scalars: &[G::ScalarField], points: &[G]) -> G {
    let affine: Vec<G::Affine> = G::normalize_batch(points);
    G::msm(&affine, scalars).expect("MSM")
}

pub struct Prover<'a, 'b, G: CurveGroup> {
    m: u64,
    cs: ProverCS<'a, 'b, G>,
}

pub struct ProverCS<'a, 'b, G: CurveGroup> {
    transcript: &'a mut Transcript,
    bp_gens: &'b BulletproofGens<G>,
    pc_gens: &'b PedersenGens<G>,
    constraints: Vec<LinearCombination<G::ScalarField>>,
    a_L: Vec<G::ScalarField>,
    a_R: Vec<G::ScalarField>,
    a_O: Vec<G::ScalarField>,
    v: Vec<G::ScalarField>,
    v_blinding: G::ScalarField,
}

impl<'a, 'b, G: CurveGroup> ConstraintSystem<G> for ProverCS<'a, 'b, G> {
    type ScalarField = G::ScalarField;

    fn multiply(
        &mut self,
        mut left: LinearCombination<G::ScalarField>,
        mut right: LinearCombination<G::ScalarField>,
    ) -> (Variable, Variable, Variable) {
        let l = self.eval(&left);
        let r = self.eval(&right);
        let o = l * r;

        let l_var = Variable::MultiplierLeft(self.a_L.len());
        let r_var = Variable::MultiplierRight(self.a_R.len());
        let o_var = Variable::MultiplierOutput(self.a_O.len());

        self.a_L.push(l);
        self.a_R.push(r);
        self.a_O.push(o);

        left.terms.push((l_var, -G::ScalarField::one()));
        right.terms.push((r_var, -G::ScalarField::one()));
        self.constrain(left);
        self.constrain(right);

        (l_var, r_var, o_var)
    }

    fn allocate<F>(&mut self, assign_fn: F) -> Result<(Variable, Variable, Variable), R1CSError>
    where
        F: FnOnce() -> Result<(G::ScalarField, G::ScalarField, G::ScalarField), R1CSError>,
    {
        let (l, r, o) = assign_fn()?;
        let l_var = Variable::MultiplierLeft(self.a_L.len());
        let r_var = Variable::MultiplierRight(self.a_R.len());
        let o_var = Variable::MultiplierOutput(self.a_O.len());
        self.a_L.push(l);
        self.a_R.push(r);
        self.a_O.push(o);
        Ok((l_var, r_var, o_var))
    }

    fn constrain(&mut self, lc: LinearCombination<G::ScalarField>) {
        self.constraints.push(lc);
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> G::ScalarField {
        <Transcript as TranscriptProtocol<G>>::challenge_scalar(self.transcript, label)
    }
}

impl<'a, 'b, G: CurveGroup> Prover<'a, 'b, G> {
    pub fn new(
        bp_gens: &'b BulletproofGens<G>,
        pc_gens: &'b PedersenGens<G>,
        transcript: &'a mut Transcript,
    ) -> Self {
        <Transcript as TranscriptProtocol<G>>::r1cs_domain_sep(transcript);

        Prover {
            m: 0,
            cs: ProverCS {
                pc_gens,
                bp_gens,
                transcript,
                v: Vec::new(),
                v_blinding: G::ScalarField::zero(),
                constraints: Vec::new(),
                a_L: Vec::new(),
                a_R: Vec::new(),
                a_O: Vec::new(),
            },
        }
    }

    pub fn commit_vec(
        &mut self,
        v: &[G::ScalarField],
        v_blinding: G::ScalarField,
        k_original: usize,
    ) -> (Vec<u8>, Vec<Variable>) {
        let start_index = self.m as usize;
        let n_padded = v.len();
        assert!(k_original <= n_padded);

        self.m += n_padded as u64;
        for &v_i in v.iter() {
            self.cs.v.push(v_i);
        }
        self.cs.v_blinding = v_blinding;

        let mut scalars: Vec<G::ScalarField> = Vec::with_capacity(1 + n_padded);
        let mut points: Vec<G> = Vec::with_capacity(1 + n_padded);

        scalars.push(v_blinding);
        points.push(self.cs.pc_gens.B_blinding);

        for (i, &vi) in v.iter().enumerate() {
            scalars.push(vi);
            points.push(self.cs.bp_gens.G_vec[0][i]);
        }

        let V = do_msm::<G>(&scalars, &points);
        let V_bytes = point_to_bytes(&V);

        <Transcript as TranscriptProtocol<G>>::commit_point(self.cs.transcript, b"V", &V_bytes);

        let vars: Vec<Variable> = (start_index..start_index + n_padded)
            .map(|i| Variable::Committed(i))
            .collect();

        (V_bytes, vars)
    }

    pub fn finalize_inputs(self) -> ProverCS<'a, 'b, G> {
        <Transcript as TranscriptProtocol<G>>::commit_u64(self.cs.transcript, b"m", self.m);
        self.cs
    }
}

impl<'a, 'b, G: CurveGroup> ProverCS<'a, 'b, G> {
    fn flattened_constraints(
        &mut self,
        z: &G::ScalarField,
    ) -> (
        Vec<G::ScalarField>,
        Vec<G::ScalarField>,
        Vec<G::ScalarField>,
        Vec<G::ScalarField>,
    ) {
        let n = self.a_L.len();
        let m = self.v.len();

        let mut wL = vec![G::ScalarField::zero(); n];
        let mut wR = vec![G::ScalarField::zero(); n];
        let mut wO = vec![G::ScalarField::zero(); n];
        let mut wV = vec![G::ScalarField::zero(); m];

        let mut exp_z = *z;
        for lc in self.constraints.iter() {
            for (var, coeff) in &lc.terms {
                match var {
                    Variable::MultiplierLeft(i) => {
                        wL[*i] += exp_z * coeff;
                    }
                    Variable::MultiplierRight(i) => {
                        wR[*i] += exp_z * coeff;
                    }
                    Variable::MultiplierOutput(i) => {
                        wO[*i] += exp_z * coeff;
                    }
                    Variable::Committed(i) => {
                        wV[*i] -= exp_z * coeff;
                    }
                    Variable::One() => {}
                }
            }
            exp_z *= z;
        }

        (wL, wR, wO, wV)
    }

    fn eval(&self, lc: &LinearCombination<G::ScalarField>) -> G::ScalarField {
        lc.terms
            .iter()
            .map(|(var, coeff)| {
                *coeff
                    * match var {
                        Variable::MultiplierLeft(i) => self.a_L[*i],
                        Variable::MultiplierRight(i) => self.a_R[*i],
                        Variable::MultiplierOutput(i) => self.a_O[*i],
                        Variable::Committed(i) => self.v[*i],
                        Variable::One() => G::ScalarField::one(),
                    }
            })
            .sum()
    }

    pub fn prove(
        mut self,
        C1_prime: &[G],
        C2_prime: &[G],
        r_prime: G::ScalarField,
        k_fold: usize,
        num_rounds: usize,
    ) -> Result<R1CSProof<G>, R1CSError> {
        let n = self.a_L.len();
        let k = self.v.len();

        if self.bp_gens.gens_capacity < k {
            return Err(R1CSError::InvalidGeneratorsLength);
        }

        let gens = self.bp_gens.share(0);

        let _do_print = std::env::var("VERBOSE").ok()
            .filter(|v| v == "1" || v.eq_ignore_ascii_case("true"))
            .is_some()
            && TIMING_PRINTED
                .compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst)
                .is_ok();
        let _t_total = Instant::now();

        // 0. Transcript & RNG
        let mut rng = ark_std::test_rng(); // For reproducibility; use OsRng for production

        // 1. Circuit Commitment 
        let _t_phase = Instant::now();
        let i_blinding = G::ScalarField::rand(&mut rng);
        let o_blinding = G::ScalarField::rand(&mut rng);
        let s_blinding = G::ScalarField::rand(&mut rng);

        let mut s_L: Vec<G::ScalarField> = (0..n).map(|_| G::ScalarField::rand(&mut rng)).collect();
        let mut s_R: Vec<G::ScalarField> = (0..n).map(|_| G::ScalarField::rand(&mut rng)).collect();
        let G_n: Vec<G> = gens.G(n).cloned().collect();
        let H_n: Vec<G> = gens.H(n).cloned().collect();

        let G_n_aff: Vec<G::Affine> = G::normalize_batch(&G_n);
        let H_n_aff: Vec<G::Affine> = G::normalize_batch(&H_n);
        let B_blinding_aff: G::Affine = self.pc_gens.B_blinding.into_affine();

        #[cfg(feature = "parallel")]
        let (A_I, A_O, S) = {
            let (A_I, (A_O, S)) = rayon::join(
                || {
                    let mut sc = vec![i_blinding];
                    sc.extend_from_slice(&self.a_L);
                    sc.extend_from_slice(&self.a_R);
                    let mut pt = vec![B_blinding_aff];
                    pt.extend_from_slice(&G_n_aff);
                    pt.extend_from_slice(&H_n_aff);
                    point_to_bytes(&G::msm(&pt, &sc).expect("MSM"))
                },
                || {
                    rayon::join(
                        || {
                            let mut sc = vec![o_blinding];
                            sc.extend_from_slice(&self.a_O);
                            let mut pt = vec![B_blinding_aff];
                            pt.extend_from_slice(&G_n_aff);
                            point_to_bytes(&G::msm(&pt, &sc).expect("MSM"))
                        },
                        || {
                            let mut sc = vec![s_blinding];
                            sc.extend_from_slice(&s_L);
                            sc.extend_from_slice(&s_R);
                            let mut pt = vec![B_blinding_aff];
                            pt.extend_from_slice(&G_n_aff);
                            pt.extend_from_slice(&H_n_aff);
                            point_to_bytes(&G::msm(&pt, &sc).expect("MSM"))
                        },
                    )
                },
            );
            (A_I, A_O, S)
        };
        #[cfg(not(feature = "parallel"))]
        let (A_I, A_O, S) = {
            let A_I = {
                let mut sc = vec![i_blinding];
                sc.extend_from_slice(&self.a_L);
                sc.extend_from_slice(&self.a_R);
                let mut pt = vec![B_blinding_aff];
                pt.extend_from_slice(&G_n_aff);
                pt.extend_from_slice(&H_n_aff);
                point_to_bytes(&G::msm(&pt, &sc).expect("MSM"))
            };
            let A_O = {
                let mut sc = vec![o_blinding];
                sc.extend_from_slice(&self.a_O);
                let mut pt = vec![B_blinding_aff];
                pt.extend_from_slice(&G_n_aff);
                point_to_bytes(&G::msm(&pt, &sc).expect("MSM"))
            };
            let S = {
                let mut sc = vec![s_blinding];
                sc.extend_from_slice(&s_L);
                sc.extend_from_slice(&s_R);
                let mut pt = vec![B_blinding_aff];
                pt.extend_from_slice(&G_n_aff);
                pt.extend_from_slice(&H_n_aff);
                point_to_bytes(&G::msm(&pt, &sc).expect("MSM"))
            };
            (A_I, A_O, S)
        };

        <Transcript as TranscriptProtocol<G>>::commit_point(self.transcript, b"A_I", &A_I);
        <Transcript as TranscriptProtocol<G>>::commit_point(self.transcript, b"A_O", &A_O);
        <Transcript as TranscriptProtocol<G>>::commit_point(self.transcript, b"S", &S);

        if _do_print {
            eprintln!(
                "  [1] Circuit commitment (A_I, A_O, S):    {:>8.3} ms",
                _t_phase.elapsed().as_secs_f64() * 1000.0
            );
        }

        // 2. Polynomial construction 
        let _t_phase = Instant::now();
        let y: G::ScalarField =
            <Transcript as TranscriptProtocol<G>>::challenge_scalar(self.transcript, b"y");
        let z: G::ScalarField =
            <Transcript as TranscriptProtocol<G>>::challenge_scalar(self.transcript, b"z");

        let (wL, wR, wO, wV) = self.flattened_constraints(&z);

        let y_inv = y.inverse().expect("y nonzero");
        let exp_y_inv: Vec<G::ScalarField> = util::exp_iter(y_inv).take(k).collect();
        let exp_y_vec: Vec<G::ScalarField> = util::exp_iter(y).take(k).collect();

        let mut l_poly = util::VecPoly3::zero(n);
        let mut r_poly = util::VecPoly3::zero(n);

        #[cfg(feature = "parallel")]
        {
            let rows: Vec<(
                G::ScalarField,
                G::ScalarField,
                G::ScalarField,
                G::ScalarField,
                G::ScalarField,
                G::ScalarField,
            )> = (0..n)
                .into_par_iter()
                .map(|i| {
                    let l1 = self.a_L[i] + exp_y_inv[i] * wR[i];
                    let l2 = self.a_O[i];
                    let l3 = s_L[i];
                    let r0 = wO[i] - exp_y_vec[i];
                    let r1 = exp_y_vec[i] * self.a_R[i] + wL[i];
                    let r3 = exp_y_vec[i] * s_R[i];
                    (l1, l2, l3, r0, r1, r3)
                })
                .collect();
            for (i, (l1, l2, l3, r0, r1, r3)) in rows.into_iter().enumerate() {
                l_poly.1[i] = l1;
                l_poly.2[i] = l2;
                l_poly.3[i] = l3;
                r_poly.0[i] = r0;
                r_poly.1[i] = r1;
                r_poly.3[i] = r3;
            }
        }
        #[cfg(not(feature = "parallel"))]
        for i in 0..n {
            l_poly.1[i] = self.a_L[i] + exp_y_inv[i] * wR[i];
            l_poly.2[i] = self.a_O[i];
            l_poly.3[i] = s_L[i];

            r_poly.0[i] = wO[i] - exp_y_vec[i];
            r_poly.1[i] = exp_y_vec[i] * self.a_R[i] + wL[i];
            r_poly.3[i] = exp_y_vec[i] * s_R[i];
        }

        let t_poly = util::VecPoly3::special_inner_product(&l_poly, &r_poly);

        if _do_print {
            eprintln!(
                "  [2] Polynomial construction (l,r,t poly): {:>8.3} ms",
                _t_phase.elapsed().as_secs_f64() * 1000.0
            );
        }

        // 3. T commitments 
        let _t_phase = Instant::now();
        let t_blindings = [
            G::ScalarField::rand(&mut rng),
            G::ScalarField::rand(&mut rng),
            G::ScalarField::rand(&mut rng),
            G::ScalarField::rand(&mut rng),
            G::ScalarField::rand(&mut rng),
        ];
        let t_2_blinding = G::ScalarField::rand(&mut rng);
        let t_2: G::ScalarField = wV.iter().zip(self.v.iter()).map(|(c, v)| *c * v).sum();

        let pc = &*self.pc_gens;
        #[cfg(feature = "parallel")]
        let (T_1, T_2, T_3, T_4, T_5, T_6) = {
            let (((T_1, T_2), (T_3, T_4)), (T_5, T_6)) = rayon::join(
                || {
                    rayon::join(
                        || {
                            rayon::join(
                                || point_to_bytes(&pc.commit(t_poly.t1, t_blindings[0])),
                                || point_to_bytes(&pc.commit(t_2, t_2_blinding)),
                            )
                        },
                        || {
                            rayon::join(
                                || point_to_bytes(&pc.commit(t_poly.t3, t_blindings[1])),
                                || point_to_bytes(&pc.commit(t_poly.t4, t_blindings[2])),
                            )
                        },
                    )
                },
                || {
                    rayon::join(
                        || point_to_bytes(&pc.commit(t_poly.t5, t_blindings[3])),
                        || point_to_bytes(&pc.commit(t_poly.t6, t_blindings[4])),
                    )
                },
            );
            (T_1, T_2, T_3, T_4, T_5, T_6)
        };
        #[cfg(not(feature = "parallel"))]
        let (T_1, T_2, T_3, T_4, T_5, T_6) = (
            point_to_bytes(&pc.commit(t_poly.t1, t_blindings[0])),
            point_to_bytes(&pc.commit(t_2, t_2_blinding)),
            point_to_bytes(&pc.commit(t_poly.t3, t_blindings[1])),
            point_to_bytes(&pc.commit(t_poly.t4, t_blindings[2])),
            point_to_bytes(&pc.commit(t_poly.t5, t_blindings[3])),
            point_to_bytes(&pc.commit(t_poly.t6, t_blindings[4])),
        );

        <Transcript as TranscriptProtocol<G>>::commit_point(self.transcript, b"T_1", &T_1);
        <Transcript as TranscriptProtocol<G>>::commit_point(self.transcript, b"T_3", &T_3);
        <Transcript as TranscriptProtocol<G>>::commit_point(self.transcript, b"T_4", &T_4);
        <Transcript as TranscriptProtocol<G>>::commit_point(self.transcript, b"T_5", &T_5);
        <Transcript as TranscriptProtocol<G>>::commit_point(self.transcript, b"T_6", &T_6);
        <Transcript as TranscriptProtocol<G>>::commit_point(self.transcript, b"T_2", &T_2);

        if _do_print {
            eprintln!(
                "  [3] T commitments (T_1..T_6):             {:>8.3} ms",
                _t_phase.elapsed().as_secs_f64() * 1000.0
            );
        }

        let _tp = Instant::now();
        let x: G::ScalarField =
            <Transcript as TranscriptProtocol<G>>::challenge_scalar(self.transcript, b"x");

        let t_x = t_poly.eval(x);
        let t_x_blinding = util::Poly6 {
            t1: t_blindings[0],
            t2: t_2_blinding,
            t3: t_blindings[1],
            t4: t_blindings[2],
            t5: t_blindings[3],
            t6: t_blindings[4],
        }
        .eval(x);

        let mut l_vec = l_poly.eval(x);
        let mut r_vec = r_poly.eval(x);

        l_vec.resize(k, G::ScalarField::zero());
        r_vec.resize(k, G::ScalarField::zero());

        for i in n..k {
            r_vec[i] = -exp_y_vec[i];
        }

        let e_blinding = x * (i_blinding + x * (o_blinding + x * s_blinding));

        <Transcript as TranscriptProtocol<G>>::commit_scalar(self.transcript, b"t_x", &t_x);
        <Transcript as TranscriptProtocol<G>>::commit_scalar(
            self.transcript,
            b"t_x_blinding",
            &t_x_blinding,
        );
        <Transcript as TranscriptProtocol<G>>::commit_scalar(
            self.transcript,
            b"e_blinding",
            &e_blinding,
        );
        if _do_print {
            eprintln!(
                "  [3.1] T commitments (t_x, e_blinding, t_x_blinding):   {:>7.1} ms",
                _tp.elapsed().as_secs_f64() * 1000.0
            );
        }

        // 4. Consistency Setup
        let _t_phase = Instant::now();
        let s_bl_prime = G::ScalarField::rand(&mut rng);
        let rnd = G::ScalarField::rand(&mut rng);
        let k_original = C1_prime.len();

        let mut s_L_prime: Vec<G::ScalarField> = (0..k_original)
            .map(|_| G::ScalarField::rand(&mut rng))
            .collect();

        let G_k: Vec<G> = gens.G(k_original).cloned().collect();

         let G_k_aff: Vec<G::Affine> = G::normalize_batch(&G_k);
        let C1_prime_aff: Vec<G::Affine> = G::normalize_batch(C1_prime);
        let C2_prime_aff: Vec<G::Affine> = G::normalize_batch(C2_prime);

        let B_aff: G::Affine = self.pc_gens.B.into_affine();
        let F_aff: G::Affine = self.pc_gens.F.into_affine();

        #[cfg(feature = "parallel")]
        let (S_prime, S1_prime, S2_prime) = {
            let (S_prime, (S1_prime, S2_prime)) = rayon::join(
                || {
                    let mut sc = vec![s_bl_prime];
                    sc.extend_from_slice(&s_L_prime[..k_original]);
                    let mut pt = vec![B_blinding_aff];
                    pt.extend_from_slice(&G_k_aff);
                    point_to_bytes(&G::msm(&pt, &sc).expect("MSM"))
                },
                || {
                    rayon::join(
                        || {
                            let mut sc = vec![rnd];
                            sc.extend_from_slice(&s_L_prime[..k_original]);
                            let mut pt = vec![B_aff];
                            pt.extend_from_slice(&C1_prime_aff);
                            point_to_bytes(&G::msm(&pt, &sc).expect("MSM"))
                        },
                        || {
                            let mut sc = vec![rnd];
                            sc.extend_from_slice(&s_L_prime[..k_original]);
                            let mut pt = vec![F_aff]; 
                            pt.extend_from_slice(&C2_prime_aff);
                            point_to_bytes(&G::msm(&pt, &sc).expect("MSM"))
                        },
                    )
                },
            );
            (S_prime, S1_prime, S2_prime)
        };
        #[cfg(not(feature = "parallel"))]
        let (S_prime, S1_prime, S2_prime) = {
            let S_prime = {
                let mut sc = vec![s_bl_prime];
                sc.extend_from_slice(&s_L_prime[..k_original]);
                let mut pt = vec![B_blinding_aff];
                pt.extend_from_slice(&G_k_aff);
                point_to_bytes(&G::msm(&pt, &sc).expect("MSM"))
            };
            let S1_prime = {
                let mut sc = vec![rnd];
                sc.extend_from_slice(&s_L_prime[..k_original]);
                let mut pt = vec![B_aff];
                pt.extend_from_slice(&C1_prime_aff);
                point_to_bytes(&G::msm(&pt, &sc).expect("MSM"))
            };
            let S2_prime = {
                let mut sc = vec![rnd];
                sc.extend_from_slice(&s_L_prime[..k_original]);
                let mut pt = vec![F_aff]; 
                pt.extend_from_slice(&C2_prime_aff);
                point_to_bytes(&G::msm(&pt, &sc).expect("MSM"))
            };
            (S_prime, S1_prime, S2_prime)
        };

        if _do_print {
            eprintln!(
                "  [4] Consistency setup (S',S1',S2'):   {:>8.3} ms",
                _t_phase.elapsed().as_secs_f64() * 1000.0
            );
        }

        let _tp = Instant::now();
        let mut lc_poly = util::VecPoly1::zero(k);
        let mut rc_poly = util::VecPoly1::zero(k);

        for _ in k_original..k {
            s_L_prime.push(G::ScalarField::zero());
        }
        for i in 0..k {
            lc_poly.0[i] = self.v[i];
            lc_poly.1[i] = s_L_prime[i];
            rc_poly.0[i] = wV[i];
        }

        let tc_poly = lc_poly.inner_product(&rc_poly);
        let t1_bl_prime = G::ScalarField::rand(&mut rng);
        let T_1_prime = point_to_bytes(&self.pc_gens.commit(tc_poly.1, t1_bl_prime));
        let tc_bl_poly = util::Poly2(t_2_blinding, t1_bl_prime, G::ScalarField::zero());

        <Transcript as TranscriptProtocol<G>>::commit_point(self.transcript, b"S_prime", &S_prime);
        <Transcript as TranscriptProtocol<G>>::commit_point(
            self.transcript,
            b"T_1_prime",
            &T_1_prime,
        );
        <Transcript as TranscriptProtocol<G>>::commit_point(
            self.transcript,
            b"S1_prime",
            &S1_prime,
        );
        <Transcript as TranscriptProtocol<G>>::commit_point(
            self.transcript,
            b"S2_prime",
            &S2_prime,
        );

        let x_prime: G::ScalarField =
            <Transcript as TranscriptProtocol<G>>::challenge_scalar(self.transcript, b"x_prime");

        let tc_x = tc_poly.eval(x_prime);
        let tc_x_blinding = tc_bl_poly.eval(x_prime);
        let ec_blinding = self.v_blinding + s_bl_prime * x_prime;
        let r_blinding = r_prime + rnd * x_prime;

        <Transcript as TranscriptProtocol<G>>::commit_scalar(self.transcript, b"tc_x", &tc_x);
        <Transcript as TranscriptProtocol<G>>::commit_scalar(
            self.transcript,
            b"tc_x_blinding",
            &tc_x_blinding,
        );
        <Transcript as TranscriptProtocol<G>>::commit_scalar(
            self.transcript,
            b"ec_blinding",
            &ec_blinding,
        );
        <Transcript as TranscriptProtocol<G>>::commit_scalar(
            self.transcript,
            b"r_blinding",
            &r_blinding,
        );

        let lc_vec = lc_poly.eval(x_prime);
        let rc_vec = rc_poly.eval(x_prime);

        if _do_print {
            eprintln!(
                "  [4.1] Consistency setup (responses):   {:>8.3} ms",
                _tp.elapsed().as_secs_f64() * 1000.0
            );
        }

        // 5. Aggregation 

        let t_cross = inner_product(&l_vec[0..k], &rc_vec) + inner_product(&lc_vec, &r_vec[0..k]);

        <Transcript as TranscriptProtocol<G>>::commit_scalar(self.transcript, b"t_cross", &t_cross);

        let x_ipp: G::ScalarField =
            <Transcript as TranscriptProtocol<G>>::challenge_scalar(self.transcript, b"x_ipp");

        let mut l_agg = Vec::with_capacity(k);
        let mut r_agg = Vec::with_capacity(k);
        for i in 0..k {
            l_agg.push(l_vec[i] + x_ipp * lc_vec[i]);
            r_agg.push(r_vec[i] + x_ipp * rc_vec[i]);
        }

        let w_agg: G::ScalarField =
            <Transcript as TranscriptProtocol<G>>::challenge_scalar(self.transcript, b"w_agg");
        let Q_agg = self.pc_gens.B * w_agg;

        let _tp = Instant::now();
        #[cfg(feature = "parallel")]
        let H_prime: Vec<G> = {
            let h_vec: Vec<G> = gens.H(k).cloned().collect();
            h_vec
                .par_iter()
                .zip(exp_y_inv.par_iter())
                .map(|(H_i, exp_i)| *H_i * *exp_i)
                .collect()
        };
        #[cfg(not(feature = "parallel"))]
        let H_prime: Vec<G> = gens
            .H(k)
            .zip(exp_y_inv.iter())
            .map(|(H_i, exp_i)| *H_i * exp_i)
            .collect();

        if _do_print {
            eprintln!(
                "  [5] Aggregation ( H'):       {:>8.3} ms",
                _tp.elapsed().as_secs_f64() * 1000.0
            );
        }

        let G_k_full: Vec<G> = self.bp_gens.G_vec[0][0..k].to_vec(); 

        // 6. IPA proof
        let _t_phase = Instant::now();
        let ipp_proof = prove_ipa::create(
            self.transcript,
            k_fold,
            &G_k_full,
            &H_prime,
            Q_agg,
            &l_agg,
            &r_agg,
            num_rounds,
        );

        if _do_print {
            eprintln!(
                "  [6] IPA proof (prove_ipa::create):    {:>8.3} ms",
                _t_phase.elapsed().as_secs_f64() * 1000.0
            );
        }

        // 7. eCP proof 

        let chall_batched_ecp: G::ScalarField =
            <Transcript as TranscriptProtocol<G>>::challenge_scalar(
                self.transcript,
                b"chall_batched_ecp",
            );

        let _t_phase = Instant::now();
        #[cfg(feature = "parallel")]
        let C_agg: Vec<G> = C1_prime
            .par_iter()
            .zip(C2_prime.par_iter())
            .map(|(c1, c2)| *c1 + *c2 * chall_batched_ecp)
            .collect();
        #[cfg(not(feature = "parallel"))]
        let C_agg: Vec<G> = C1_prime
            .iter()
            .zip(C2_prime.iter())
            .map(|(c1, c2)| *c1 + *c2 * chall_batched_ecp)
            .collect();
        if _do_print {
            eprintln!(
                "  [7] (C_agg):    {:>8.3} ms",
                _t_phase.elapsed().as_secs_f64() * 1000.0
            );
        }

        let _tp = Instant::now();
        let ecp_batched = prove_ecp::create(
            self.transcript,
            k_fold,
            &G_k_full,
            &C_agg,
            &lc_vec,
            num_rounds,
        );

        if _do_print {
            eprintln!(
                "  [8] eCP proof (prove_ecp::create):       {:>8.3} ms",
                _tp.elapsed().as_secs_f64() * 1000.0
            );
            eprintln!("  ─────────────────────────────────────────────────────");
            eprintln!(
                "  TOTAL prove():                              {:>8.3} ms  (n={}, k={})",
                _t_total.elapsed().as_secs_f64() * 1000.0,
                n,
                k
            );
            eprintln!();
        }

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
