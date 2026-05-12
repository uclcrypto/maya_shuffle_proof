//! Verifier implementation for the R1CS shuffle proof.

use ark_ec::CurveGroup;
use ark_ff::{Field, One, UniformRand, Zero};
use ark_serialize::CanonicalDeserialize;
use ark_serialize::Valid;
use merlin::Transcript;
use std::iter;

use super::{ConstraintSystem, LinearCombination, R1CSProof, Variable};
use crate::errors::R1CSError;
use crate::generators::{BulletproofGens, PedersenGens};
use crate::inner_product_proof::inner_product;
use crate::transcript::TranscriptProtocol;
use crate::util;

fn decompress_point<G: CurveGroup>(bytes: &[u8]) -> Result<G::Affine, R1CSError> {
    G::Affine::deserialize_compressed(bytes).map_err(|_| R1CSError::VerificationError)
}

pub struct Verifier<'a, 'b, G: CurveGroup> {
    m: u64,
    cs: VerifierCS<'a, 'b, G>,
}

pub struct VerifierCS<'a, 'b, G: CurveGroup> {
    bp_gens: &'b BulletproofGens<G>,
    pc_gens: &'b PedersenGens<G>,
    transcript: &'a mut Transcript,
    constraints: Vec<LinearCombination<G::ScalarField>>,
    num_vars: usize,
    V: Vec<Vec<u8>>, 
    num_inputs: usize,
}

impl<'a, 'b, G: CurveGroup> ConstraintSystem<G> for VerifierCS<'a, 'b, G> {
    type ScalarField = G::ScalarField;

    fn multiply(
        &mut self,
        mut left: LinearCombination<G::ScalarField>,
        mut right: LinearCombination<G::ScalarField>,
    ) -> (Variable, Variable, Variable) {
        let var = self.num_vars;
        self.num_vars += 1;

        let l_var = Variable::MultiplierLeft(var);
        let r_var = Variable::MultiplierRight(var);
        let o_var = Variable::MultiplierOutput(var);

        left.terms.push((l_var, -G::ScalarField::one()));
        right.terms.push((r_var, -G::ScalarField::one()));
        self.constrain(left);
        self.constrain(right);

        (l_var, r_var, o_var)
    }

    fn allocate<F>(&mut self, _assign_fn: F) -> Result<(Variable, Variable, Variable), R1CSError>
    where
        F: FnOnce() -> Result<(G::ScalarField, G::ScalarField, G::ScalarField), R1CSError>,
    {
        let var = self.num_vars;
        self.num_vars += 1;
        Ok((
            Variable::MultiplierLeft(var),
            Variable::MultiplierRight(var),
            Variable::MultiplierOutput(var),
        ))
    }

    fn constrain(&mut self, lc: LinearCombination<G::ScalarField>) {
        self.constraints.push(lc);
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> G::ScalarField {
        <Transcript as TranscriptProtocol<G>>::challenge_scalar(self.transcript, label)
    }
}

impl<'a, 'b, G: CurveGroup> Verifier<'a, 'b, G> {
    pub fn new(
        bp_gens: &'b BulletproofGens<G>,
        pc_gens: &'b PedersenGens<G>,
        transcript: &'a mut Transcript,
    ) -> Self {
        <Transcript as TranscriptProtocol<G>>::r1cs_domain_sep(transcript);

        Verifier {
            m: 0,
            cs: VerifierCS {
                bp_gens,
                pc_gens,
                transcript,
                constraints: Vec::new(),
                num_vars: 0,
                V: Vec::new(),
                num_inputs: 0,
            },
        }
    }

    pub fn commit_vec(
        &mut self,
        commitment: Vec<u8>, 
        k: usize,
    ) -> Vec<Variable> {
        let start = self.m as usize;
        self.m += k as u64;
        self.cs.V.push(commitment.clone());
        self.cs.num_inputs = k;

        <Transcript as TranscriptProtocol<G>>::commit_point(self.cs.transcript, b"V", &commitment);

        (start..start + k).map(|i| Variable::Committed(i)).collect()
    }

    pub fn finalize_inputs(self) -> VerifierCS<'a, 'b, G> {
        <Transcript as TranscriptProtocol<G>>::commit_u64(self.cs.transcript, b"m", self.m);
        self.cs
    }
}

impl<'a, 'b, G: CurveGroup> VerifierCS<'a, 'b, G> {
    fn flattened_constraints(
        &mut self,
        z: &G::ScalarField,
    ) -> (
        Vec<G::ScalarField>,
        Vec<G::ScalarField>,
        Vec<G::ScalarField>,
        Vec<G::ScalarField>,
        G::ScalarField,
    ) {
        let n = self.num_vars;
        let m = self.num_inputs;

        let mut wL = vec![G::ScalarField::zero(); n];
        let mut wR = vec![G::ScalarField::zero(); n];
        let mut wO = vec![G::ScalarField::zero(); n];
        let mut wV = vec![G::ScalarField::zero(); m];
        let mut wc = G::ScalarField::zero();

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
                    Variable::One() => {
                        wc -= exp_z * coeff;
                    }
                }
            }
            exp_z *= z;
        }

        (wL, wR, wO, wV, wc)
    }

    pub fn verify(
        mut self,
        proof: &R1CSProof<G>,
        C1_prime: &[G],
        C2_prime: &[G],
        C: &[G],
    ) -> Result<(), R1CSError> {
        let n = self.num_vars;
        let padded_n = self.num_inputs;
        let k_fold = proof.ipp_proof.k;
        let pad = padded_n - n;

        if self.bp_gens.gens_capacity < padded_n {
            return Err(R1CSError::InvalidGeneratorsLength);
        }

        let gens = self.bp_gens.share(0);

        // 2. Transcript Interaction
        <Transcript as TranscriptProtocol<G>>::commit_point(self.transcript, b"A_I", &proof.A_I);
        <Transcript as TranscriptProtocol<G>>::commit_point(self.transcript, b"A_O", &proof.A_O);
        <Transcript as TranscriptProtocol<G>>::commit_point(self.transcript, b"S", &proof.S);

        let y: G::ScalarField =
            <Transcript as TranscriptProtocol<G>>::challenge_scalar(self.transcript, b"y");
        let z: G::ScalarField =
            <Transcript as TranscriptProtocol<G>>::challenge_scalar(self.transcript, b"z");

        <Transcript as TranscriptProtocol<G>>::commit_point(self.transcript, b"T_1", &proof.T_1);
        <Transcript as TranscriptProtocol<G>>::commit_point(self.transcript, b"T_3", &proof.T_3);
        <Transcript as TranscriptProtocol<G>>::commit_point(self.transcript, b"T_4", &proof.T_4);
        <Transcript as TranscriptProtocol<G>>::commit_point(self.transcript, b"T_5", &proof.T_5);
        <Transcript as TranscriptProtocol<G>>::commit_point(self.transcript, b"T_6", &proof.T_6);
        <Transcript as TranscriptProtocol<G>>::commit_point(self.transcript, b"T_2", &proof.T_2);

        let x: G::ScalarField =
            <Transcript as TranscriptProtocol<G>>::challenge_scalar(self.transcript, b"x");

        <Transcript as TranscriptProtocol<G>>::commit_scalar(self.transcript, b"t_x", &proof.t_x);
        <Transcript as TranscriptProtocol<G>>::commit_scalar(
            self.transcript,
            b"t_x_blinding",
            &proof.t_x_blinding,
        );
        <Transcript as TranscriptProtocol<G>>::commit_scalar(
            self.transcript,
            b"e_blinding",
            &proof.e_blinding,
        );

        let (wL, wR, wO, wV, wc) = self.flattened_constraints(&z);

        <Transcript as TranscriptProtocol<G>>::commit_point(
            self.transcript,
            b"S_prime",
            &proof.S_prime,
        );
        <Transcript as TranscriptProtocol<G>>::commit_point(
            self.transcript,
            b"T_1_prime",
            &proof.T_1_prime,
        );
        <Transcript as TranscriptProtocol<G>>::commit_point(
            self.transcript,
            b"S1_prime",
            &proof.S1_prime,
        );
        <Transcript as TranscriptProtocol<G>>::commit_point(
            self.transcript,
            b"S2_prime",
            &proof.S2_prime,
        );

        let x_prime: G::ScalarField =
            <Transcript as TranscriptProtocol<G>>::challenge_scalar(self.transcript, b"x_prime");

        <Transcript as TranscriptProtocol<G>>::commit_scalar(self.transcript, b"tc_x", &proof.tc_x);
        <Transcript as TranscriptProtocol<G>>::commit_scalar(
            self.transcript,
            b"tc_x_blinding",
            &proof.tc_x_blinding,
        );
        <Transcript as TranscriptProtocol<G>>::commit_scalar(
            self.transcript,
            b"ec_blinding",
            &proof.ec_blinding,
        );
        <Transcript as TranscriptProtocol<G>>::commit_scalar(
            self.transcript,
            b"r_blinding",
            &proof.r_blinding,
        );
        <Transcript as TranscriptProtocol<G>>::commit_scalar(
            self.transcript,
            b"t_cross",
            &proof.t_cross,
        );

        let t_cross = proof.t_cross;
        let x_ipp: G::ScalarField =
            <Transcript as TranscriptProtocol<G>>::challenge_scalar(self.transcript, b"x_ipp");
        let w_agg: G::ScalarField =
            <Transcript as TranscriptProtocol<G>>::challenge_scalar(self.transcript, b"w_agg");

        // 3. Scalar & Point Reconstruction
        let (s_g_cir, s_h_cir, s_Q_cir, s_P_cir, s_U_cir) = proof
            .ipp_proof
            .verification_scalars(padded_n, self.transcript)
            .map_err(|_| R1CSError::VerificationError)?;

        let mut U_points_decompressed: Vec<G::Affine> = Vec::new();
        for r in 0..proof.ipp_proof.U_vecs.len() {
            for i_list in 0..(2 * k_fold - 2) {
                let pt = decompress_point::<G>(&proof.ipp_proof.U_vecs[r][i_list])
                    .map_err(|_| R1CSError::VerificationError)?;
                U_points_decompressed.push(pt);
            }
        }

        let y_inv = y.inverse().expect("y nonzero");
        let y_inv_vec: Vec<G::ScalarField> = util::exp_iter(y_inv).take(padded_n).collect();

        let yneg_wR: Vec<G::ScalarField> = wR
            .into_iter()
            .zip(y_inv_vec.iter())
            .map(|(wRi, exp_y_inv)| wRi * exp_y_inv)
            .chain(iter::repeat(G::ScalarField::zero()).take(pad))
            .collect();

        let delta = inner_product(&yneg_wR[0..n], &wL);

        let g_scalars: Vec<G::ScalarField> = s_g_cir
            .iter()
            .zip(yneg_wR.iter())
            .map(|(s_g_i, yneg_wR_i)| *s_g_i - x * yneg_wR_i * s_P_cir)
            .collect();

        let rC: Vec<G::ScalarField> = wV.to_vec();

        let h_scalars: Vec<G::ScalarField> = s_h_cir
            .iter()
            .zip(y_inv_vec.iter())
            .zip(
                wL.into_iter()
                    .chain(iter::repeat(G::ScalarField::zero()).take(pad)),
            )
            .zip(
                wO.into_iter()
                    .chain(iter::repeat(G::ScalarField::zero()).take(pad)),
            )
            .zip(rC.iter())
            .map(|((((s_h_i, y_inv_i), wLi), wOi), rCi)| {
                let term1 = *y_inv_i * s_h_i;
                let term2 = (*y_inv_i * (x * wLi + wOi) - G::ScalarField::one()) * (-s_P_cir);
                let term3 = *y_inv_i * x_ipp * (-s_P_cir) * rCi;
                term1 + term2 + term3
            })
            .collect();

        // 4. Verification Check Setup
        let mut rng = ark_std::test_rng();
        let r: G::ScalarField = G::ScalarField::rand(&mut rng);

        let xx = x * x;
        let rxx = r * xx;
        let xxx = x * xx;
        let r2 = r * r;

        let T_scalars = [r * x, r * xx, rxx * x, rxx * xx, rxx * xxx, rxx * xx * xx];
        let T_point_bytes = [
            &proof.T_1, &proof.T_2, &proof.T_3, &proof.T_4, &proof.T_5, &proof.T_6,
        ];

        let expected_ip = proof.t_x + x_ipp * t_cross + x_ipp * x_ipp * proof.tc_x;

        let B_scalar = w_agg * s_Q_cir - w_agg * expected_ip * s_P_cir
            + r * (xx * (wc + delta) - proof.t_x)
            - r2 * proof.tc_x;

        let B_blinding_scalar = x_ipp * proof.ec_blinding * s_P_cir + proof.e_blinding * s_P_cir
            - r2 * proof.tc_x_blinding
            - r * proof.t_x_blinding;

        let chall_batched_ecp: G::ScalarField =
            <Transcript as TranscriptProtocol<G>>::challenge_scalar(
                self.transcript,
                b"chall_batched_ecp",
            );

        let r3 = r2 * r;
        let r4 = r3 * r;

        let (z_s_vec, s_P, s_A_vec) = proof
            .ecp_batched
            .verification_scalars(padded_n, self.transcript)
            .map_err(|_| R1CSError::VerificationError)?;

        let s_V_checkS = r4 * (-s_P);
        let s_S_prime_checkS = r4 * x_prime * (-s_P);
        let s_S1_prime = r3 * x_prime * (-s_P);
        let s_S2_prime = r3 * chall_batched_ecp * x_prime * (-s_P);
        let s_B_checkS = s_P * r3 * proof.r_blinding;
        let s_C0 = r3 * (-s_P);
        let s_C1 = r3 * chall_batched_ecp * (-s_P);
        let s_B_blinding_checkS = s_P * r4 * proof.ec_blinding;
        let s_F_checkS = s_P * r3 * chall_batched_ecp * proof.r_blinding;

        let final_scalar_V = (-x_ipp * s_P_cir) + s_V_checkS;
        let final_scalar_S_prime = (-x_ipp * s_P_cir * x_prime) + s_S_prime_checkS;
        let final_scalar_B = B_scalar + s_B_checkS;
        let final_scalar_B_blinding = B_blinding_scalar + s_B_blinding_checkS;

        let final_g_scalars: Vec<G::ScalarField> = g_scalars
            .iter()
            .zip(z_s_vec.iter())
            .map(|(g_i, z_i)| *g_i + (*z_i * r4))
            .collect();

        // 5. Final MSM Construction
        let k_original = C1_prime.len();

        let C1_prime_aff: Vec<G::Affine> = G::normalize_batch(C1_prime);
        let C2_prime_aff: Vec<G::Affine> = G::normalize_batch(C2_prime);
        let C_aff: Vec<G::Affine> = G::normalize_batch(C);

        for aff in C1_prime_aff
            .iter()
            .chain(C2_prime_aff.iter())
            .chain(C_aff.iter())
        {
            if aff.check().is_err() {
                return Err(R1CSError::VerificationError);
            }
        }

        let G_padded_proj: Vec<G> = gens.G(padded_n).cloned().collect();
        let H_padded_proj: Vec<G> = gens.H(padded_n).cloned().collect();
        let G_padded_aff: Vec<G::Affine> = G::normalize_batch(&G_padded_proj);
        let H_padded_aff: Vec<G::Affine> = G::normalize_batch(&H_padded_proj);

        let B_aff: G::Affine = self.pc_gens.B.into_affine();
        let B_blinding_aff: G::Affine = self.pc_gens.B_blinding.into_affine();
        let F_aff: G::Affine = self.pc_gens.F.into_affine();

        let mut combined_scalars: Vec<G::ScalarField> = Vec::new();
        let mut combined_points: Vec<G::Affine> = Vec::new();

        combined_scalars.push(-x * s_P_cir);
        combined_points.push(decompress_point::<G>(&proof.A_I)?);

        combined_scalars.push(-x * x * s_P_cir);
        combined_points.push(decompress_point::<G>(&proof.A_O)?);

        combined_scalars.push(-x * x * x * s_P_cir);
        combined_points.push(decompress_point::<G>(&proof.S)?);

        combined_scalars.push(final_scalar_V);
        combined_points.push(decompress_point::<G>(&self.V[0])?);
        combined_scalars.push(final_scalar_S_prime);
        combined_points.push(decompress_point::<G>(&proof.S_prime)?);

        combined_scalars.push(final_scalar_B);
        combined_points.push(B_aff);
        combined_scalars.push(final_scalar_B_blinding);
        combined_points.push(B_blinding_aff);
        combined_scalars.push(s_F_checkS);
        combined_points.push(F_aff);

        for (i, g) in G_padded_aff.iter().enumerate() {
            combined_scalars.push(final_g_scalars[i]);
            combined_points.push(*g);
        }

        for (i, h) in H_padded_aff.iter().enumerate() {
            combined_scalars.push(h_scalars[i]);
            combined_points.push(*h);
        }

        for (i, u) in U_points_decompressed.iter().enumerate() {
            combined_scalars.push(-s_U_cir[i]);
            combined_points.push(*u);
        }

        combined_scalars.push(r2 * x_prime);
        combined_points.push(decompress_point::<G>(&proof.T_1_prime)?);
        combined_scalars.push(r2);
        combined_points.push(decompress_point::<G>(&proof.T_2)?);

        for (i, t_bytes) in T_point_bytes.iter().enumerate() {
            combined_scalars.push(T_scalars[i]);
            combined_points.push(decompress_point::<G>(t_bytes)?);
        }

        combined_scalars.push(s_S1_prime);
        combined_points.push(decompress_point::<G>(&proof.S1_prime)?);
        combined_scalars.push(s_S2_prime);
        combined_points.push(decompress_point::<G>(&proof.S2_prime)?);

        combined_scalars.push(s_C0);
        combined_points.push(C_aff[0]);
        combined_scalars.push(s_C1);
        combined_points.push(C_aff[1]);

        for i in 0..k_original {
            combined_scalars.push(z_s_vec[i] * r3);
            combined_points.push(C1_prime_aff[i]);
        }
        for i in 0..k_original {
            combined_scalars.push(z_s_vec[i] * r3 * chall_batched_ecp);
            combined_points.push(C2_prime_aff[i]);
        }

        let mut all_A0: Vec<G::Affine> = Vec::new();
        let mut all_A1: Vec<G::Affine> = Vec::new();
        for round_vec in proof.ecp_batched.A_vecs.iter() {
            for pair in round_vec.iter() {
                all_A0.push(decompress_point::<G>(&pair[0])?);
                all_A1.push(decompress_point::<G>(&pair[1])?);
            }
        }

        for (i, pt) in all_A0.iter().enumerate() {
            combined_scalars.push(-s_A_vec[i] * r4);
            combined_points.push(*pt);
        }
        for (i, pt) in all_A1.iter().enumerate() {
            combined_scalars.push(-s_A_vec[i] * r3);
            combined_points.push(*pt);
        }

        // 6. Final Execution
        let mega_check = G::msm(&combined_points, &combined_scalars).expect("MSM");

        if !mega_check.is_zero() {
            return Err(R1CSError::VerificationError);
        }

        Ok(())
    }
}
