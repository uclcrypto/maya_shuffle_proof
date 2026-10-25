
#![allow(non_snake_case)]

use ark_ec::CurveGroup;
use ark_ff::{Field, One, PrimeField, Zero};
use ark_serialize::CanonicalSerialize;
use merlin::Transcript;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Instant;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

use crate::errors::ProofError;
use crate::generators::{fold_pad_generators, HashToGroup};
use crate::transcript::{point_to_bytes, TranscriptProtocol};

static IPP_TIMING_PRINTED: AtomicBool = AtomicBool::new(false);

pub(crate) const IPA_PAD_G_DOMAIN: &[u8] = b"MAYA-ipa-pad-g-v1";
pub(crate) const IPA_PAD_H_DOMAIN: &[u8] = b"MAYA-ipa-pad-h-v1";
pub(crate) const ECP_PAD_G_DOMAIN: &[u8] = b"MAYA-ecp-pad-G-v1";
pub(crate) const MAX_FOLD_FACTOR: usize = 64;
pub(crate) const MAX_FOLD_ROUNDS: usize = 64;


fn scalar_pow<F: PrimeField>(base: F, mut exp: u64) -> F {
    let mut result = F::one();
    let mut b = base;
    while exp > 0 {
        if (exp & 1) == 1 {
            result *= b;
        }
        b *= b;
        exp >>= 1;
    }
    result
}

#[cfg(test)]
pub(crate) fn fold_pad_counts(n: usize, k: usize, d: usize) -> Vec<usize> {
    let lengths = reconstruct_round_lengths(n, k, d);
    (0..d).map(|r| lengths[r + 1] * k - lengths[r]).collect()
}

pub(crate) fn pad_seed(transcript: &mut Transcript, round: usize) -> [u8; 32] {
    transcript.append_message(b"pad_round", &(round as u64).to_le_bytes());
    let mut seed = [0u8; 32];
    transcript.challenge_bytes(b"pad_seed", &mut seed);
    seed
}


fn reconstruct_round_lengths(mut n: usize, k: usize, d: usize) -> Vec<usize> {
    let mut lengths = Vec::with_capacity(d + 1);
    lengths.push(n);
    for _ in 0..d {
        let rem = n % k;
        let pad = if rem == 0 { 0 } else { k - rem };
        let n_padded = n + pad;
        n = n_padded / k;
        lengths.push(n);
    }
    lengths
}

fn msm_affine<G: CurveGroup>(scalars: &[G::ScalarField], points: &[G::Affine]) -> G {
    crate::vartime_msm::vartime_multiscalar_mul::<G>(scalars, points)
}


//  prove_ipa (IPA with Iterative Padding)
#[derive(Clone, Debug)]
pub struct prove_ipa<G: CurveGroup> {
    pub k: usize,
    /// Cross-term commitments per round
    pub U_vecs: Vec<Vec<Vec<u8>>>,
    /// Final witness vector a
    pub a_final: Vec<G::ScalarField>,
    /// Final witness vector b
    pub b_final: Vec<G::ScalarField>,
}

impl<G: CurveGroup> prove_ipa<G> {
    pub fn create(
        transcript: &mut Transcript,
        k: usize,
        g_vec: &[G],
        h_vec: &[G],
        Q_point: G,
        a_vec: &[G::ScalarField],
        b_vec: &[G::ScalarField],
       num_rounds: usize,
    ) -> prove_ipa<G>
    where
        G: HashToGroup,
    {
        let _do_print = std::env::var("VERBOSE").ok()
            .filter(|v| v == "1" || v.eq_ignore_ascii_case("true"))
            .is_some()
            && IPP_TIMING_PRINTED
                .compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst)
                .is_ok();
        let _t_total = Instant::now();

        let n = a_vec.len();
        assert_eq!(g_vec.len(), n);
        assert_eq!(h_vec.len(), n);
        assert_eq!(b_vec.len(), n);
        assert!(k > 1, "k must be greater than 1");

        let _t_phase: Instant = Instant::now();

        transcript.append_message(b"protocol-name", b"k_bullet_delay");
        transcript.append_message(b"n", &(n as u64).to_le_bytes());
        transcript.append_message(b"k", &(k as u64).to_le_bytes());

        let mut g_curr = g_vec.to_vec();
        let mut h_curr = h_vec.to_vec();
        let mut a_curr = a_vec.to_vec();
        let mut b_curr = b_vec.to_vec();

        let mut U_vecs: Vec<Vec<Vec<u8>>> = Vec::with_capacity(num_rounds);

        #[cfg(not(feature = "parallel"))]
        let mut scalars_l: Vec<G::ScalarField> = Vec::with_capacity(2 * n);
        #[cfg(not(feature = "parallel"))]
        let mut points_l: Vec<G::Affine> = Vec::with_capacity(2 * n);
        #[cfg(not(feature = "parallel"))]
        let mut scalars_neg_l: Vec<G::ScalarField> = Vec::with_capacity(2 * n);
        #[cfg(not(feature = "parallel"))]
        let mut points_neg_l: Vec<G::Affine> = Vec::with_capacity(2 * n);

        let mut n_j = n;

        for j in 0..num_rounds {
            let _t_round = Instant::now();

            let rem = n_j % k;
            if rem != 0 {
                let pad = k - rem;
                a_curr.extend(std::iter::repeat(G::ScalarField::zero()).take(pad));
                b_curr.extend(std::iter::repeat(G::ScalarField::zero()).take(pad));
                let seed = pad_seed(transcript, j);
                g_curr.extend(fold_pad_generators::<G>(IPA_PAD_G_DOMAIN, &seed, pad));
                h_curr.extend(fold_pad_generators::<G>(IPA_PAD_H_DOMAIN, &seed, pad));
                n_j += pad;
            }

            let m_j = n_j / k;

            let _t_norm = Instant::now();
                #[cfg(feature = "parallel")]
            let (g_curr_aff, h_curr_aff): (Vec<G::Affine>, Vec<G::Affine>) = rayon::join(
                || G::normalize_batch(&g_curr),
                || G::normalize_batch(&h_curr),
            );
            #[cfg(not(feature = "parallel"))]
            let (g_curr_aff, h_curr_aff) =
                (G::normalize_batch(&g_curr), G::normalize_batch(&h_curr));

            let _t_cross = Instant::now();
            let a_splits: Vec<&[G::ScalarField]> = a_curr.chunks(m_j).collect();
            let b_splits: Vec<&[G::ScalarField]> = b_curr.chunks(m_j).collect();
            let g_splits: Vec<&[G::Affine]> = g_curr_aff.chunks(m_j).collect();
            let h_splits: Vec<&[G::Affine]> = h_curr_aff.chunks(m_j).collect();

            #[cfg(feature = "parallel")]
            let (U_pos_compressed, U_neg_compressed): (Vec<Vec<u8>>, Vec<Vec<u8>>) = (1..k)
                .into_par_iter()
                .map(|l| {
                    let cap = 2 * (k - l) * m_j;
                    let mut v_pos_l = G::ScalarField::zero();
                    let mut v_neg_l = G::ScalarField::zero();
                    let mut sc_pos: Vec<G::ScalarField> = Vec::with_capacity(cap);
                    let mut pt_pos: Vec<G::Affine> = Vec::with_capacity(cap);
                    let mut sc_neg: Vec<G::ScalarField> = Vec::with_capacity(cap);
                    let mut pt_neg: Vec<G::Affine> = Vec::with_capacity(cap);
                    for i in 0..(k - l) {
                        v_pos_l += inner_product(a_splits[i], b_splits[i + l]);
                        sc_pos.extend_from_slice(a_splits[i]);
                        pt_pos.extend_from_slice(g_splits[i + l]);
                        sc_pos.extend_from_slice(b_splits[i + l]);
                        pt_pos.extend_from_slice(h_splits[i]);
                        v_neg_l += inner_product(a_splits[i + l], b_splits[i]);
                        sc_neg.extend_from_slice(a_splits[i + l]);
                        pt_neg.extend_from_slice(g_splits[i]);
                        sc_neg.extend_from_slice(b_splits[i]);
                        pt_neg.extend_from_slice(h_splits[i + l]);
                    }
                    let (U_l, U_neg_l) = rayon::join(
                        || msm_affine::<G>(&sc_pos, &pt_pos) + Q_point * v_pos_l,
                        || msm_affine::<G>(&sc_neg, &pt_neg) + Q_point * v_neg_l,
                    );
                    (point_to_bytes(&U_l), point_to_bytes(&U_neg_l))
                })
                .unzip();

            #[cfg(not(feature = "parallel"))]
            let (U_pos_compressed, U_neg_compressed): (Vec<Vec<u8>>, Vec<Vec<u8>>) = {
                let mut pos = Vec::with_capacity(k - 1);
                let mut neg = Vec::with_capacity(k - 1);
                for l in 1..k {
                    let mut v_pos_l = G::ScalarField::zero();
                    let mut v_neg_l = G::ScalarField::zero();
                    scalars_l.clear();
                    points_l.clear();
                    scalars_neg_l.clear();
                    points_neg_l.clear();
                    for i in 0..(k - l) {
                        v_pos_l += inner_product(a_splits[i], b_splits[i + l]);
                        scalars_l.extend_from_slice(a_splits[i]);
                        points_l.extend_from_slice(g_splits[i + l]);
                        scalars_l.extend_from_slice(b_splits[i + l]);
                        points_l.extend_from_slice(h_splits[i]);
                        v_neg_l += inner_product(a_splits[i + l], b_splits[i]);
                        scalars_neg_l.extend_from_slice(a_splits[i + l]);
                        points_neg_l.extend_from_slice(g_splits[i]);
                        scalars_neg_l.extend_from_slice(b_splits[i]);
                        points_neg_l.extend_from_slice(h_splits[i + l]);
                    }
                    let U_l = msm_affine::<G>(&scalars_l, &points_l) + Q_point * v_pos_l;
                    let U_neg_l =
                        msm_affine::<G>(&scalars_neg_l, &points_neg_l) + Q_point * v_neg_l;
                    pos.push(point_to_bytes(&U_l));
                    neg.push(point_to_bytes(&U_neg_l));
                }
                (pos, neg)
            };

            let _t_transcript = Instant::now();
            let mut U_vec_round = U_pos_compressed;
            U_vec_round.extend(U_neg_compressed);

            for (idx, point_bytes) in U_vec_round.iter().enumerate() {
                transcript.append_message(b"U_round", &(j as u64).to_le_bytes());
                transcript.append_message(b"U_index", &(idx as u64).to_le_bytes());
                <Transcript as TranscriptProtocol<G>>::commit_point(
                    transcript,
                    b"U_point",
                    point_bytes,
                );
            }
            U_vecs.push(U_vec_round);

            transcript.append_message(b"challenge_prefix", b"c_");
            transcript.append_message(b"challenge_index", &(j as u64).to_le_bytes());
            let c: G::ScalarField = <Transcript as TranscriptProtocol<G>>::challenge_scalar(
                transcript,
                b"challenge_separator",
            );
            let c_inv = c.inverse().expect("challenge must be nonzero");

            let _t_wit = Instant::now();
            let mut c_powers_a: Vec<G::ScalarField> = Vec::with_capacity(k);
            let mut c_pow_y = G::ScalarField::one();
            for _ in 0..k {
                c_powers_a.push(c_pow_y);
                c_pow_y *= c;
            }

            let mut c_powers_b: Vec<G::ScalarField> = Vec::with_capacity(k);
            let mut c_pow_x = G::ScalarField::one();
            for _ in 1..k {
                c_pow_x *= c;
            }
            for _ in 0..k {
                c_powers_b.push(c_pow_x);
                c_pow_x *= c_inv;
            }

            let g_scalars = &c_powers_b;
            let h_scalars = &c_powers_a;

            let mut a_new = vec![G::ScalarField::zero(); m_j];
            let mut b_new = vec![G::ScalarField::zero(); m_j];
            let mut g_new_proj: Vec<G> = vec![G::zero(); m_j];
            let mut h_new_proj: Vec<G> = vec![G::zero(); m_j];

            #[cfg(feature = "parallel")]
            {
                a_new
                    .par_iter_mut()
                    .zip(b_new.par_iter_mut())
                    .zip(g_new_proj.par_iter_mut())
                    .zip(h_new_proj.par_iter_mut())
                    .enumerate()
                    .for_each(|(j_item, (((a_out, b_out), g_out), h_out))| {
                        let mut a_j_acc = G::ScalarField::zero();
                        let mut b_j_acc = G::ScalarField::zero();
                        let mut g_col: Vec<G::Affine> = Vec::with_capacity(k);
                        let mut h_col: Vec<G::Affine> = Vec::with_capacity(k);
                        for i in 0..k {
                            a_j_acc += a_splits[i][j_item] * c_powers_a[i];
                            b_j_acc += b_splits[i][j_item] * c_powers_b[i];
                            g_col.push(g_splits[i][j_item]);
                            h_col.push(h_splits[i][j_item]);
                        }
                        *a_out = a_j_acc;
                        *b_out = b_j_acc;
                        *g_out =
                            crate::vartime_msm::vartime_multiscalar_mul::<G>(g_scalars, &g_col);
                        *h_out =
                            crate::vartime_msm::vartime_multiscalar_mul::<G>(h_scalars, &h_col);
                    });
            }
            #[cfg(not(feature = "parallel"))]
            {
                let mut g_col_aff: Vec<G::Affine> = Vec::with_capacity(k);
                let mut h_col_aff: Vec<G::Affine> = Vec::with_capacity(k);
                for j_item in 0..m_j {
                    let mut a_j_acc = G::ScalarField::zero();
                    let mut b_j_acc = G::ScalarField::zero();
                    g_col_aff.clear();
                    h_col_aff.clear();
                    for i in 0..k {
                        a_j_acc += a_splits[i][j_item] * c_powers_a[i];
                        b_j_acc += b_splits[i][j_item] * c_powers_b[i];
                        g_col_aff.push(g_splits[i][j_item]);
                        h_col_aff.push(h_splits[i][j_item]);
                    }
                    a_new[j_item] = a_j_acc;
                    b_new[j_item] = b_j_acc;
                    g_new_proj[j_item] =
                        crate::vartime_msm::vartime_multiscalar_mul::<G>(g_scalars, &g_col_aff);
                    h_new_proj[j_item] =
                        crate::vartime_msm::vartime_multiscalar_mul::<G>(h_scalars, &h_col_aff);
                }
            }

            a_curr = a_new;
            b_curr = b_new;
            g_curr = g_new_proj;
            h_curr = h_new_proj;
            n_j = m_j;
        }

        prove_ipa {
            k,
            U_vecs,
            a_final: a_curr,
            b_final: b_curr,
        }
    }

    pub fn verification_scalars(
        &self,
        n: usize,
        transcript: &mut Transcript,
    ) -> Result<
        (
            Vec<G::ScalarField>, 
            Vec<G::ScalarField>, 
            G::ScalarField,      
            G::ScalarField,     
            Vec<G::ScalarField>, 
            Vec<G::ScalarField>,
            Vec<G>,
        ),
        ProofError,
    >
    where
        G: HashToGroup,
    {
        let k = self.k;
        if n == 0 {
            return Err(ProofError::InvalidGeneratorsLength);
        }
        let d = self.U_vecs.len();
        if k < 2
            || k > MAX_FOLD_FACTOR
            || d > MAX_FOLD_ROUNDS
            || self.U_vecs.iter().any(|round| round.len() != 2 * k - 2)
        {
            return Err(ProofError::FormatError);
        }

        let round_lengths = reconstruct_round_lengths(n, k, d);
        let m = *round_lengths.last().unwrap();

        if self.a_final.len() != m || self.b_final.len() != m {
            return Err(ProofError::VerificationError);
        }

        transcript.append_message(b"protocol-name", b"k_bullet_delay");
        transcript.append_message(b"n", &(n as u64).to_le_bytes());
        transcript.append_message(b"k", &(k as u64).to_le_bytes());

        let mut challenges: Vec<G::ScalarField> = Vec::with_capacity(d);
        let mut pad_points: Vec<G> = Vec::new();
        let mut h_pad_points: Vec<G> = Vec::new();

        for r in 0..d {
            let pad = round_lengths[r + 1] * k - round_lengths[r];
            if pad > 0 {
                let seed = pad_seed(transcript, r);
                pad_points.extend(fold_pad_generators::<G>(IPA_PAD_G_DOMAIN, &seed, pad));
                h_pad_points.extend(fold_pad_generators::<G>(IPA_PAD_H_DOMAIN, &seed, pad));
            }
            for i_list in 0..(2 * k - 2) {
                transcript.append_message(b"U_round", &(r as u64).to_le_bytes());
                transcript.append_message(b"U_index", &(i_list as u64).to_le_bytes());
                <Transcript as TranscriptProtocol<G>>::commit_point(
                    transcript,
                    b"U_point",
                    &self.U_vecs[r][i_list],
                );
            }
            transcript.append_message(b"challenge_prefix", b"c_");
            transcript.append_message(b"challenge_index", &(r as u64).to_le_bytes());
            challenges.push(<Transcript as TranscriptProtocol<G>>::challenge_scalar(
                transcript,
                b"challenge_separator",
            ));
        }

        let mut challenges_inv = challenges.clone();
        ark_ff::batch_inversion(&mut challenges_inv);

        let k_minus_1_exp = (k - 1) as u64;
        let mut c_k_minus_1_products = vec![G::ScalarField::one(); d];
        let mut product_so_far = G::ScalarField::one();
        for r in (0..d).rev() {
            let c_k_minus_1 = scalar_pow(challenges[r], k_minus_1_exp);
            c_k_minus_1_products[r] = product_so_far;
            product_so_far *= c_k_minus_1;
        }
        let s_P = product_so_far;

        let mut s_g_pad_rounds: Vec<Vec<G::ScalarField>> = vec![Vec::new(); d];
        let mut s_h_pad_rounds: Vec<Vec<G::ScalarField>> = vec![Vec::new(); d];

        let mut s_g_full = self.a_final.clone();
        for r in (0..d).rev() {
            let c_inv = challenges_inv[r];
            let mut block = Vec::with_capacity(k);
            let mut val = G::ScalarField::one();
            for _ in 0..k {
                block.push(val);
                val *= c_inv;
            }

            let mut next_s = Vec::with_capacity(s_g_full.len() * k);
            for b in block.iter() {
                for val in s_g_full.iter() {
                    next_s.push(*val * b);
                }
            }
            s_g_pad_rounds[r] = next_s.split_off(round_lengths[r]);
            s_g_full = next_s;
        }
        for x in s_g_full.iter_mut() {
            *x *= s_P;
        }

        let mut s_h_full = self.b_final.clone();
        for r in (0..d).rev() {
            let c = challenges[r];
            let mut block = Vec::with_capacity(k);
            let mut val = G::ScalarField::one();
            for _ in 0..k {
                block.push(val);
                val *= c;
            }

            let mut next_s = Vec::with_capacity(s_h_full.len() * k);
            for b in block.iter() {
                for val in s_h_full.iter() {
                    next_s.push(*val * b);
                }
            }
            s_h_pad_rounds[r] = next_s.split_off(round_lengths[r]);
            s_h_full = next_s;
        }

        let s_Q_final = inner_product(&self.a_final, &self.b_final);

        let mut s_U: Vec<G::ScalarField> = Vec::with_capacity(d * (2 * k - 2));
        for r in 0..d {
            let c_r = challenges[r];
            let suffix_prod = c_k_minus_1_products[r];
            for l in 1..k {
                let exp = (k - 1 - l) as u64;
                s_U.push(scalar_pow(c_r, exp) * suffix_prod);
            }
            for l in 1..k {
                let exp = (k - 1 + l) as u64;
                s_U.push(scalar_pow(c_r, exp) * suffix_prod);
            }
        }

        let mut s_pad: Vec<G::ScalarField> = Vec::with_capacity(2 * pad_points.len());
        for r in 0..d {
            let factor = c_k_minus_1_products[r] * scalar_pow(challenges[r], k_minus_1_exp);
            s_pad.extend(s_g_pad_rounds[r].iter().map(|x| *x * factor));
        }
        s_pad.extend(s_h_pad_rounds.into_iter().flatten());
        pad_points.extend(h_pad_points);

        Ok((s_g_full, s_h_full, s_Q_final, s_P, s_U, s_pad, pad_points))
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        buf.extend_from_slice(&(self.k as u64).to_le_bytes());
        let d = self.U_vecs.len();
        buf.extend_from_slice(&(d as u64).to_le_bytes());
        let m = self.a_final.len();
        buf.extend_from_slice(&(m as u64).to_le_bytes());
        for round_vec in self.U_vecs.iter() {
            for point_bytes in round_vec.iter() {
                buf.extend_from_slice(&(point_bytes.len() as u32).to_le_bytes());
                buf.extend_from_slice(point_bytes);
            }
        }
        let mut sbuf = Vec::new();
        for s in self.a_final.iter().chain(self.b_final.iter()) {
            sbuf.clear();
            s.serialize_compressed(&mut sbuf)
                .expect("scalar serialization");
            buf.extend_from_slice(&(sbuf.len() as u32).to_le_bytes());
            buf.extend_from_slice(&sbuf);
        }
        buf
    }

    pub fn from_bytes(slice: &[u8]) -> Result<prove_ipa<G>, ProofError> {
        use ark_serialize::CanonicalDeserialize;
        let b = slice.len();
        if b < 24 {
            return Err(ProofError::FormatError);
        }
        let mut pos = 0;

        let k = u64::from_le_bytes(
            slice[pos..pos + 8]
                .try_into()
                .map_err(|_| ProofError::FormatError)?,
        ) as usize;
        pos += 8;
        let d = u64::from_le_bytes(
            slice[pos..pos + 8]
                .try_into()
                .map_err(|_| ProofError::FormatError)?,
        ) as usize;
        pos += 8;
        let m = u64::from_le_bytes(
            slice[pos..pos + 8]
                .try_into()
                .map_err(|_| ProofError::FormatError)?,
        ) as usize;
        pos += 8;

        if k < 2 || k > MAX_FOLD_FACTOR || d > MAX_FOLD_ROUNDS || m == 0 {
            return Err(ProofError::FormatError);
        }
        let min_len = m
            .checked_mul(2)
            .and_then(|s| s.checked_add(d * (2 * k - 2)))
            .and_then(|w| w.checked_mul(4))
            .and_then(|w| w.checked_add(24))
            .ok_or(ProofError::FormatError)?;
        if b < min_len {
            return Err(ProofError::FormatError);
        }

        let points_per_round = 2 * k - 2;
        let mut U_vecs = Vec::with_capacity(d);
        for _ in 0..d {
            let mut round = Vec::with_capacity(points_per_round);
            for _ in 0..points_per_round {
                if pos + 4 > b {
                    return Err(ProofError::FormatError);
                }
                let len = u32::from_le_bytes(
                    slice[pos..pos + 4]
                        .try_into()
                        .map_err(|_| ProofError::FormatError)?,
                ) as usize;
                pos += 4;
                if pos + len > b {
                    return Err(ProofError::FormatError);
                }
                round.push(slice[pos..pos + len].to_vec());
                pos += len;
            }
            U_vecs.push(round);
        }

        let mut a_final = Vec::with_capacity(m);
        for _ in 0..m {
            if pos + 4 > b {
                return Err(ProofError::FormatError);
            }
            let len = u32::from_le_bytes(
                slice[pos..pos + 4]
                    .try_into()
                    .map_err(|_| ProofError::FormatError)?,
            ) as usize;
            pos += 4;
            if pos + len > b {
                return Err(ProofError::FormatError);
            }
            let s = G::ScalarField::deserialize_compressed(&slice[pos..pos + len])
                .map_err(|_| ProofError::FormatError)?;
            a_final.push(s);
            pos += len;
        }

        let mut b_final = Vec::with_capacity(m);
        for _ in 0..m {
            if pos + 4 > b {
                return Err(ProofError::FormatError);
            }
            let len = u32::from_le_bytes(
                slice[pos..pos + 4]
                    .try_into()
                    .map_err(|_| ProofError::FormatError)?,
            ) as usize;
            pos += 4;
            if pos + len > b {
                return Err(ProofError::FormatError);
            }
            let s = G::ScalarField::deserialize_compressed(&slice[pos..pos + len])
                .map_err(|_| ProofError::FormatError)?;
            b_final.push(s);
            pos += len;
        }

       if pos != b {
            return Err(ProofError::FormatError);
        }

        Ok(prove_ipa {
            k,
            U_vecs,
            a_final,
            b_final,
        })
    }
}

//  prove_ecp (eCP with Iterative Padding)

#[derive(Clone, Debug)]
pub struct prove_ecp<G: CurveGroup> {
    pub k: usize,
    pub A_vecs: Vec<Vec<[Vec<u8>; 2]>>,
    pub z: Vec<G::ScalarField>,
}

impl<G: CurveGroup> prove_ecp<G> {
    pub fn create(
        transcript: &mut Transcript,
        k: usize,
        G_vec: &[G],
        C1_vec: &[G],
        a_vec: &[G::ScalarField],
        num_rounds: usize,
    ) -> prove_ecp<G>
    where
        G: HashToGroup,
    {
        let _t_total = Instant::now();

        let n = a_vec.len();

        let _t_phase = Instant::now();

        let mut a_curr = a_vec.to_vec();
        let mut G_curr = G_vec.to_vec();
        let mut C1_curr = C1_vec.to_vec();

        if C1_curr.len() < n {
            C1_curr.resize(n, G::zero());
        }

        transcript.append_message(b"protocol-name", b"k_ipp_delay_2");
        transcript.append_message(b"n", &(n as u64).to_le_bytes());
        transcript.append_message(b"k", &(k as u64).to_le_bytes());

        let mut A_vecs: Vec<Vec<[Vec<u8>; 2]>> = Vec::with_capacity(num_rounds);

        #[cfg(not(feature = "parallel"))]
        let mut scalars_0: Vec<G::ScalarField> = Vec::with_capacity(n);
        #[cfg(not(feature = "parallel"))]
        let mut points_0: Vec<G::Affine> = Vec::with_capacity(n);
        #[cfg(not(feature = "parallel"))]
        let mut scalars_1: Vec<G::ScalarField> = Vec::with_capacity(n);
        #[cfg(not(feature = "parallel"))]
        let mut points_1: Vec<G::Affine> = Vec::with_capacity(n);

        let mut n_j = n;

        for round_idx in 0..num_rounds {
            let rem = n_j % k;
            if rem != 0 {
                let pad = k - rem;
                a_curr.extend(std::iter::repeat(G::ScalarField::zero()).take(pad));
                let seed = pad_seed(transcript, round_idx);
                G_curr.extend(fold_pad_generators::<G>(ECP_PAD_G_DOMAIN, &seed, pad));
                C1_curr.extend(std::iter::repeat(G::zero()).take(pad));
                n_j += pad;
            }

            let m_j = n_j / k;

            let _t_norm = Instant::now();
            #[cfg(feature = "parallel")]
            let (G_curr_aff, C1_curr_aff): (Vec<G::Affine>, Vec<G::Affine>) = rayon::join(
                || G::normalize_batch(&G_curr),
                || G::normalize_batch(&C1_curr),
            );
            #[cfg(not(feature = "parallel"))]
            let (G_curr_aff, C1_curr_aff) =
                (G::normalize_batch(&G_curr), G::normalize_batch(&C1_curr));

            let _t_cross = Instant::now();
            let a_splits: Vec<&[G::ScalarField]> = a_curr.chunks(m_j).collect();
            let G_splits: Vec<&[G::Affine]> = G_curr_aff.chunks(m_j).collect();
            let C1_splits: Vec<&[G::Affine]> = C1_curr_aff.chunks(m_j).collect();

            #[cfg(feature = "parallel")]
            let A_vecs_round: Vec<[Vec<u8>; 2]> = {
                let first_half: Vec<[Vec<u8>; 2]> = (1..k)
                    .into_par_iter()
                    .map(|i| {
                        let cap = i * m_j;
                        let mut sc0: Vec<G::ScalarField> = Vec::with_capacity(cap);
                        let mut pt0: Vec<G::Affine> = Vec::with_capacity(cap);
                        let mut sc1: Vec<G::ScalarField> = Vec::with_capacity(cap);
                        let mut pt1: Vec<G::Affine> = Vec::with_capacity(cap);
                        for l in 1..(i + 1) {
                            sc0.extend_from_slice(a_splits[l - 1]);
                            pt0.extend_from_slice(G_splits[k - i + l - 1]);
                            sc1.extend_from_slice(a_splits[l - 1]);
                            pt1.extend_from_slice(C1_splits[k - i + l - 1]);
                        }
                        let (p0, p1) = rayon::join(
                            || msm_affine::<G>(&sc0, &pt0),
                            || msm_affine::<G>(&sc1, &pt1),
                        );
                        [point_to_bytes(&p0), point_to_bytes(&p1)]
                    })
                    .collect();
                let second_half: Vec<[Vec<u8>; 2]> = (1..k)
                    .into_par_iter()
                    .map(|i| {
                        let cap = (k - i) * m_j;
                        let mut sc0: Vec<G::ScalarField> = Vec::with_capacity(cap);
                        let mut pt0: Vec<G::Affine> = Vec::with_capacity(cap);
                        let mut sc1: Vec<G::ScalarField> = Vec::with_capacity(cap);
                        let mut pt1: Vec<G::Affine> = Vec::with_capacity(cap);
                        for l in 1..(k - i + 1) {
                            sc0.extend_from_slice(a_splits[i + l - 1]);
                            pt0.extend_from_slice(G_splits[l - 1]);
                            sc1.extend_from_slice(a_splits[i + l - 1]);
                            pt1.extend_from_slice(C1_splits[l - 1]);
                        }
                        let (p0, p1) = rayon::join(
                            || msm_affine::<G>(&sc0, &pt0),
                            || msm_affine::<G>(&sc1, &pt1),
                        );
                        [point_to_bytes(&p0), point_to_bytes(&p1)]
                    })
                    .collect();
                first_half.into_iter().chain(second_half).collect()
            };

            #[cfg(not(feature = "parallel"))]
            let mut A_vecs_round: Vec<[Vec<u8>; 2]> = Vec::with_capacity(2 * k - 2);
            #[cfg(not(feature = "parallel"))]
            for i in 1..k {
                scalars_0.clear();
                points_0.clear();
                scalars_1.clear();
                points_1.clear();
                for l in 1..(i + 1) {
                    scalars_0.extend_from_slice(a_splits[l - 1]);
                    points_0.extend_from_slice(G_splits[k - i + l - 1]);
                    scalars_1.extend_from_slice(a_splits[l - 1]);
                    points_1.extend_from_slice(C1_splits[k - i + l - 1]);
                }
                let p0 = msm_affine::<G>(&scalars_0, &points_0);
                let p1 = msm_affine::<G>(&scalars_1, &points_1);
                A_vecs_round.push([point_to_bytes(&p0), point_to_bytes(&p1)]);
            }
            #[cfg(not(feature = "parallel"))]
            for i in 1..k {
                scalars_0.clear();
                points_0.clear();
                scalars_1.clear();
                points_1.clear();
                for l in 1..(k - i + 1) {
                    scalars_0.extend_from_slice(a_splits[i + l - 1]);
                    points_0.extend_from_slice(G_splits[l - 1]);
                    scalars_1.extend_from_slice(a_splits[i + l - 1]);
                    points_1.extend_from_slice(C1_splits[l - 1]);
                }
                let p0 = msm_affine::<G>(&scalars_0, &points_0);
                let p1 = msm_affine::<G>(&scalars_1, &points_1);
                A_vecs_round.push([point_to_bytes(&p0), point_to_bytes(&p1)]);
            }

            let _t_transcript = Instant::now();
            for (idx, point_pair) in A_vecs_round.iter().enumerate() {
                transcript.append_message(b"A_round", &(round_idx as u64).to_le_bytes());
                transcript.append_message(b"A_index", &(idx as u64).to_le_bytes());
                <Transcript as TranscriptProtocol<G>>::commit_point(
                    transcript,
                    b"A_point_0",
                    &point_pair[0],
                );
                <Transcript as TranscriptProtocol<G>>::commit_point(
                    transcript,
                    b"A_point_1",
                    &point_pair[1],
                );
            }
            A_vecs.push(A_vecs_round);

            transcript.append_message(b"challenge_prefix", b"c_");
            transcript.append_message(b"challenge_index", &(round_idx as u64).to_le_bytes());
            let c: G::ScalarField = <Transcript as TranscriptProtocol<G>>::challenge_scalar(
                transcript,
                b"challenge_separator",
            );

            let _t_wit = Instant::now();
            let mut c_powers_a: Vec<G::ScalarField> = Vec::with_capacity(k);
            let mut c_pow = G::ScalarField::one();
            for _ in 0..k {
                c_powers_a.push(c_pow);
                c_pow *= c;
            }

            let c_inv = c.inverse().expect("challenge nonzero");
            let mut c_powers_bases: Vec<G::ScalarField> = Vec::with_capacity(k);
            let mut c_pow_exp = scalar_pow(c, k as u64);
            for _ in 0..k {
                c_powers_bases.push(c_pow_exp);
                c_pow_exp *= c_inv;
            }

            let mut a_new = vec![G::ScalarField::zero(); m_j];
            let mut G_new_proj: Vec<G> = vec![G::zero(); m_j];
            let mut C1_new_proj: Vec<G> = vec![G::zero(); m_j];

            #[cfg(feature = "parallel")]
            {
                a_new
                    .par_iter_mut()
                    .zip(G_new_proj.par_iter_mut())
                    .zip(C1_new_proj.par_iter_mut())
                    .enumerate()
                    .for_each(|(j_item, ((a_out, g_out), c1_out))| {
                        let mut a_acc = G::ScalarField::zero();
                        let mut g_col: Vec<G::Affine> = Vec::with_capacity(k);
                        let mut c1_col: Vec<G::Affine> = Vec::with_capacity(k);
                        for i in 0..k {
                            a_acc += a_splits[i][j_item] * c_powers_a[i];
                            g_col.push(G_splits[i][j_item]);
                            c1_col.push(C1_splits[i][j_item]);
                        }
                        *a_out = a_acc;
                        *g_out = crate::vartime_msm::vartime_multiscalar_mul::<G>(
                            &c_powers_bases,
                            &g_col,
                        );
                        *c1_out = crate::vartime_msm::vartime_multiscalar_mul::<G>(
                            &c_powers_bases,
                            &c1_col,
                        );
                    });
            }
            #[cfg(not(feature = "parallel"))]
            {
                let mut g_col_aff: Vec<G::Affine> = Vec::with_capacity(k);
                let mut c1_col_aff: Vec<G::Affine> = Vec::with_capacity(k);
                for j_item in 0..m_j {
                    let mut a_acc = G::ScalarField::zero();
                    g_col_aff.clear();
                    c1_col_aff.clear();
                    for i in 0..k {
                        a_acc += a_splits[i][j_item] * c_powers_a[i];
                        g_col_aff.push(G_splits[i][j_item]);
                        c1_col_aff.push(C1_splits[i][j_item]);
                    }
                    a_new[j_item] = a_acc;
                    G_new_proj[j_item] = crate::vartime_msm::vartime_multiscalar_mul::<G>(
                        &c_powers_bases,
                        &g_col_aff,
                    );
                    C1_new_proj[j_item] = crate::vartime_msm::vartime_multiscalar_mul::<G>(
                        &c_powers_bases,
                        &c1_col_aff,
                    );
                }
            }

            a_curr = a_new;
            G_curr = G_new_proj;
            C1_curr = C1_new_proj;
            n_j = m_j;
        }

        prove_ecp {
            k,
            A_vecs,
            z: a_curr,
        }
    }

    pub fn verification_scalars(
        &self,
        n: usize,
        transcript: &mut Transcript,
    ) -> Result<
        (
            Vec<G::ScalarField>,
            G::ScalarField,
            Vec<G::ScalarField>,
            Vec<G::ScalarField>,
            Vec<G>,
        ),
        ProofError,
    >
    where
        G: HashToGroup,
    {
        let k = self.k;
        if n == 0 {
            return Err(ProofError::InvalidGeneratorsLength);
        }
        let d = self.A_vecs.len();
        if k < 2
            || k > MAX_FOLD_FACTOR
            || d > MAX_FOLD_ROUNDS
            || self.A_vecs.iter().any(|round| round.len() != 2 * k - 2)
        {
            return Err(ProofError::FormatError);
        }

        let round_lengths = reconstruct_round_lengths(n, k, d);
        let m = *round_lengths.last().unwrap();

        if self.z.len() != m {
            return Err(ProofError::VerificationError);
        }

        transcript.append_message(b"protocol-name", b"k_ipp_delay_2");
        transcript.append_message(b"n", &(n as u64).to_le_bytes());
        transcript.append_message(b"k", &(k as u64).to_le_bytes());

        let mut challenges: Vec<G::ScalarField> = Vec::with_capacity(d);
        let mut pad_points: Vec<G> = Vec::new();
        for r in 0..d {
            let pad = round_lengths[r + 1] * k - round_lengths[r];
            if pad > 0 {
                let seed = pad_seed(transcript, r);
                pad_points.extend(fold_pad_generators::<G>(ECP_PAD_G_DOMAIN, &seed, pad));
            }
            for i_list in 0..(2 * k - 2) {
                let tuple = &self.A_vecs[r][i_list];
                transcript.append_message(b"A_round", &(r as u64).to_le_bytes());
                transcript.append_message(b"A_index", &(i_list as u64).to_le_bytes());
                <Transcript as TranscriptProtocol<G>>::commit_point(
                    transcript,
                    b"A_point_0",
                    &tuple[0],
                );
                <Transcript as TranscriptProtocol<G>>::commit_point(
                    transcript,
                    b"A_point_1",
                    &tuple[1],
                );
            }
            transcript.append_message(b"challenge_prefix", b"c_");
            transcript.append_message(b"challenge_index", &(r as u64).to_le_bytes());
            challenges.push(<Transcript as TranscriptProtocol<G>>::challenge_scalar(
                transcript,
                b"challenge_separator",
            ));
        }

        let mut challenges_inv = challenges.clone();
        ark_ff::batch_inversion(&mut challenges_inv);

        let k_exp = k as u64;
        let mut c_k_products = vec![G::ScalarField::one(); d];
        let mut product_so_far = G::ScalarField::one();
        for r in (0..d).rev() {
            let c_k = scalar_pow(challenges[r], k_exp);
            c_k_products[r] = product_so_far;
            product_so_far *= c_k;
        }
        let s_P = product_so_far;

        let mut z_s_pad_rounds: Vec<Vec<G::ScalarField>> = vec![Vec::new(); d];

        let mut z_s_vec = self.z.clone();
        for r in (0..d).rev() {
            let c_inv = challenges_inv[r];
            let mut block = Vec::with_capacity(k);
            let mut val = G::ScalarField::one();
            for _ in 0..k {
                block.push(val);
                val *= c_inv;
            }

            let mut next_s = Vec::with_capacity(z_s_vec.len() * k);
            for b in block.iter() {
                for z_val in z_s_vec.iter() {
                    next_s.push(*z_val * b);
                }
            }
            z_s_pad_rounds[r] = next_s.split_off(round_lengths[r]);
            z_s_vec = next_s;
        }
        for x in z_s_vec.iter_mut() {
            *x *= s_P;
        }

        let mut s_A_vec: Vec<G::ScalarField> = Vec::with_capacity(d * (2 * k - 2));
        for r in 0..d {
            let c_r = challenges[r];
            let suffix_prod = c_k_products[r];
            for i in 1..k {
                s_A_vec.push(scalar_pow(c_r, i as u64) * suffix_prod);
            }
            for i in 1..k {
                s_A_vec.push(scalar_pow(c_r, (k + i) as u64) * suffix_prod);
            }
        }

        let mut z_s_pad: Vec<G::ScalarField> = Vec::new();
        for r in 0..d {
            let factor = c_k_products[r] * scalar_pow(challenges[r], k_exp);
            z_s_pad.extend(z_s_pad_rounds[r].iter().map(|x| *x * factor));
        }

        Ok((z_s_vec, s_P, s_A_vec, z_s_pad, pad_points))
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        buf.extend_from_slice(&(self.k as u64).to_le_bytes());
        let d = self.A_vecs.len();
        buf.extend_from_slice(&(d as u64).to_le_bytes());
        let m = self.z.len();
        buf.extend_from_slice(&(m as u64).to_le_bytes());
        for round_vec in self.A_vecs.iter() {
            for pair in round_vec.iter() {
                buf.extend_from_slice(&(pair[0].len() as u32).to_le_bytes());
                buf.extend_from_slice(&pair[0]);
                buf.extend_from_slice(&(pair[1].len() as u32).to_le_bytes());
                buf.extend_from_slice(&pair[1]);
            }
        }
        let mut sbuf = Vec::new();
        for s in self.z.iter() {
            sbuf.clear();
            s.serialize_compressed(&mut sbuf)
                .expect("scalar serialization");
            buf.extend_from_slice(&(sbuf.len() as u32).to_le_bytes());
            buf.extend_from_slice(&sbuf);
        }
        buf
    }

    pub fn from_bytes(slice: &[u8]) -> Result<prove_ecp<G>, ProofError> {
        use ark_serialize::CanonicalDeserialize;
        let b = slice.len();
        if b < 24 {
            return Err(ProofError::FormatError);
        }
        let mut pos = 0;

        let k = u64::from_le_bytes(
            slice[pos..pos + 8]
                .try_into()
                .map_err(|_| ProofError::FormatError)?,
        ) as usize;
        pos += 8;
        let d = u64::from_le_bytes(
            slice[pos..pos + 8]
                .try_into()
                .map_err(|_| ProofError::FormatError)?,
        ) as usize;
        pos += 8;
        let m = u64::from_le_bytes(
            slice[pos..pos + 8]
                .try_into()
                .map_err(|_| ProofError::FormatError)?,
        ) as usize;
        pos += 8;

        if k < 2 || k > MAX_FOLD_FACTOR || d > MAX_FOLD_ROUNDS || m == 0 {
            return Err(ProofError::FormatError);
        }
        let min_len = m
            .checked_add(d * (4 * k - 4))
            .and_then(|w| w.checked_mul(4))
            .and_then(|w| w.checked_add(24))
            .ok_or(ProofError::FormatError)?;
        if b < min_len {
            return Err(ProofError::FormatError);
        }

        let pairs_per_round = 2 * k - 2;
        let mut A_vecs = Vec::with_capacity(d);
        for _ in 0..d {
            let mut round = Vec::with_capacity(pairs_per_round);
            for _ in 0..pairs_per_round {
                if pos + 4 > b {
                    return Err(ProofError::FormatError);
                }
                let len0 = u32::from_le_bytes(
                    slice[pos..pos + 4]
                        .try_into()
                        .map_err(|_| ProofError::FormatError)?,
                ) as usize;
                pos += 4;
                if pos + len0 > b {
                    return Err(ProofError::FormatError);
                }
                let p0 = slice[pos..pos + len0].to_vec();
                pos += len0;

                if pos + 4 > b {
                    return Err(ProofError::FormatError);
                }
                let len1 = u32::from_le_bytes(
                    slice[pos..pos + 4]
                        .try_into()
                        .map_err(|_| ProofError::FormatError)?,
                ) as usize;
                pos += 4;
                if pos + len1 > b {
                    return Err(ProofError::FormatError);
                }
                let p1 = slice[pos..pos + len1].to_vec();
                pos += len1;

                round.push([p0, p1]);
            }
            A_vecs.push(round);
        }

        let mut z = Vec::with_capacity(m);
        for _ in 0..m {
            if pos + 4 > b {
                return Err(ProofError::FormatError);
            }
            let len = u32::from_le_bytes(
                slice[pos..pos + 4]
                    .try_into()
                    .map_err(|_| ProofError::FormatError)?,
            ) as usize;
            pos += 4;
            if pos + len > b {
                return Err(ProofError::FormatError);
            }
            let s = G::ScalarField::deserialize_compressed(&slice[pos..pos + len])
                .map_err(|_| ProofError::FormatError)?;
            z.push(s);
            pos += len;
        }
            if pos != b {
            return Err(ProofError::FormatError);
        }

        Ok(prove_ecp { k, A_vecs, z })
    }
}


pub fn inner_product<F: PrimeField>(a: &[F], b: &[F]) -> F {
    assert_eq!(a.len(), b.len(), "inner_product: vector lengths must match");
    let mut out = F::zero();
    for i in 0..a.len() {
        out += a[i] * b[i];
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ec::{AffineRepr, VariableBaseMSM};
    use ark_secp256r1::{Fr, Projective as P};
    use ark_serialize::CanonicalDeserialize;
    use ark_std::UniformRand;

    
     fn points(n: usize) -> Vec<P> {
        let mut rng = rand::thread_rng();
        (0..n).map(|_| P::rand(&mut rng)).collect()
    }

    fn scalars(n: usize) -> Vec<Fr> {
        let mut rng = rand::thread_rng();
        (0..n).map(|_| Fr::rand(&mut rng)).collect()
    }

    fn msm(s: &[Fr], p: &[P]) -> P {
        P::msm(&P::normalize_batch(p), s).unwrap()
    }

    fn decompress(bytes: &[u8]) -> Option<P> {
        <P as CurveGroup>::Affine::deserialize_compressed(bytes)
            .ok()
            .map(|a| a.into_group())
    }

    fn rounds(mut n: usize, k: usize) -> usize {
        let mut d = 0;
        while n > 1 {
            n = (n + (k - n % k) % k) / k;
            d += 1;
        }
        d
    }
    
    // A prover that writes delta into the padding slot of round `round` (The forgery the identity padding generators would allow)
    fn forging_ipa(
        k: usize,
        g_vec: &[P],
        h_vec: &[P],
        q: P,
        a_vec: &[Fr],
        b_vec: &[Fr],
        num_rounds: usize,
        round: usize,
        delta: Fr,
    ) -> prove_ipa<P> {
        let transcript = &mut Transcript::new(b"ipa-test");
        let n = a_vec.len();
        transcript.append_message(b"protocol-name", b"k_bullet_delay");
        transcript.append_message(b"n", &(n as u64).to_le_bytes());
        transcript.append_message(b"k", &(k as u64).to_le_bytes());
        let counts = fold_pad_counts(n, k, num_rounds);
        let mut g = g_vec.to_vec();
        let mut h = h_vec.to_vec();
        let mut a = a_vec.to_vec();
        let mut b = b_vec.to_vec();
         let mut gap = delta;
        let mut U_vecs = Vec::with_capacity(num_rounds);
        for j in 0..num_rounds {
            if counts[j] > 0 {
                let start = a.len();
                a.extend(std::iter::repeat(Fr::zero()).take(counts[j]));
                b.extend(std::iter::repeat(Fr::zero()).take(counts[j]));
                let seed = pad_seed(transcript, j);
                 g.extend(fold_pad_generators::<P>(IPA_PAD_G_DOMAIN, &seed, counts[j]));
                h.extend(fold_pad_generators::<P>(IPA_PAD_H_DOMAIN, &seed, counts[j]));
                if round == j {
                    a[start] = gap;
                    b[start] = Fr::one();
                    gap = Fr::zero();
                }
            }
            let m = a.len() / k;
            let a_s: Vec<&[Fr]> = a.chunks(m).collect();
            let b_s: Vec<&[Fr]> = b.chunks(m).collect();
            let g_s: Vec<&[P]> = g.chunks(m).collect();
            let h_s: Vec<&[P]> = h.chunks(m).collect();
            let mut pos = Vec::with_capacity(k - 1);
            let mut neg = Vec::with_capacity(k - 1);
            for l in 1..k {
                let mut u_pos = P::zero();
                let mut u_neg = P::zero();
                for i in 0..(k - l) {
                    u_pos += msm(a_s[i], g_s[i + l])
                        + msm(b_s[i + l], h_s[i])
                        + q * inner_product(a_s[i], b_s[i + l]);
                    u_neg += msm(a_s[i + l], g_s[i])
                        + msm(b_s[i], h_s[i + l])
                        + q * inner_product(a_s[i + l], b_s[i]);
                }
                pos.push(u_pos);
                neg.push(u_neg);
            }
            let mut round_points: Vec<Vec<u8>> = pos.iter().map(|p| point_to_bytes(p)).collect();
            round_points.extend(neg.iter().map(|p| point_to_bytes(p)));
            for (idx, point) in round_points.iter().enumerate() {
                transcript.append_message(b"U_round", &(j as u64).to_le_bytes());
                transcript.append_message(b"U_index", &(idx as u64).to_le_bytes());
                <Transcript as TranscriptProtocol<P>>::commit_point(transcript, b"U_point", point);
            }
            U_vecs.push(round_points);
            transcript.append_message(b"challenge_prefix", b"c_");
            transcript.append_message(b"challenge_index", &(j as u64).to_le_bytes());
            let c: Fr = <Transcript as TranscriptProtocol<P>>::challenge_scalar(
                transcript,
                b"challenge_separator",
            );
            
            let c_inv = c.inverse().unwrap();
            let mut a_new = vec![Fr::zero(); m];
            let mut b_new = vec![Fr::zero(); m];
            let mut g_new = vec![P::zero(); m];
            let mut h_new = vec![P::zero(); m];
            for i in 0..k {
                let c_i = scalar_pow(c, i as u64);
                let c_rev = scalar_pow(c, (k - 1) as u64) * scalar_pow(c_inv, i as u64);
                for t in 0..m {
                    a_new[t] += a_s[i][t] * c_i;
                    b_new[t] += b_s[i][t] * c_rev;
                    g_new[t] += g_s[i][t] * c_rev;
                    h_new[t] += h_s[i][t] * c_i;
                }
            }
            a = a_new;
            b = b_new;
            g = g_new;
            h = h_new;
            gap *= scalar_pow(c, (k - 1) as u64);
        }
        prove_ipa {
            k,
            U_vecs,
            a_final: a,
            b_final: b,
        }
    }

    fn ipa_check(proof: &prove_ipa<P>, n: usize, g: &[P], h: &[P], q: P, p: P) -> bool {
        let mut transcript = Transcript::new(b"ipa-test");
        let (s_g, s_h, s_q, s_p, s_u, s_pad, pad_points) =
            match proof.verification_scalars(n, &mut transcript) {
                Ok(v) => v,
                Err(_) => return false,
            };
        let u: Option<Vec<P>> = proof.U_vecs.iter().flatten().map(|u| decompress(u)).collect();
        let u = match u {
            Some(u) => u,
            None => return false,
        };
        p * s_p + msm(&s_u, &u) == msm(&s_g, g) + msm(&s_h, h) + q * s_q + msm(&s_pad, &pad_points)
    }

    fn ecp_check(proof: &prove_ecp<P>, n: usize, g: &[P], c: &[P], p_g: P, p_c: P) -> bool {
        let mut transcript = Transcript::new(b"ecp-test");
        let (z_s, s_p, s_a, z_pad, g_pad) = match proof.verification_scalars(n, &mut transcript) {
            Ok(v) => v,
            Err(_) => return false,
        };
        let a0: Option<Vec<P>> = proof.A_vecs.iter().flatten().map(|a| decompress(&a[0])).collect();
        let a1: Option<Vec<P>> = proof.A_vecs.iter().flatten().map(|a| decompress(&a[1])).collect();
        let (a0, a1) = match (a0, a1) {
            (Some(a0), Some(a1)) => (a0, a1),
            _ => return false,
        };
        msm(&z_s, g) + msm(&z_pad, &g_pad) == p_g * s_p + msm(&s_a, &a0)
            && msm(&z_s[..c.len()], c) == p_c * s_p + msm(&s_a, &a1)
    }

    const CONFIGS: [(usize, usize); 4] = [(10, 4), (21, 3), (130, 5), (33, 2)];

    fn statement(n: usize, delta: Fr) -> (Vec<P>, Vec<P>, P, Vec<Fr>, Vec<Fr>, P) {
        let (g, h, q) = (points(n), points(n), points(1)[0]);
        let (a, b) = (scalars(n), scalars(n));
        let p = msm(&a, &g) + msm(&b, &h) + q * (inner_product(&a, &b) + delta);
        (g, h, q, a, b, p)
    }

    
    #[test]
    fn honest_padded_proofs_verify() {
        for &(n, k) in CONFIGS.iter() {
            let d = rounds(n, k);
            let (g, h, q, a, b, p) = statement(n, Fr::zero());
            let proof =
                prove_ipa::<P>::create(&mut Transcript::new(b"ipa-test"), k, &g, &h, q, &a, &b, d);
            assert!(ipa_check(&proof, n, &g, &h, q, p));
            assert!(!ipa_check(&proof, n, &g, &h, q, p + q));
        }
    }

    #[test]
    fn padding_slot_forgery_is_rejected() {
        for &(n, k) in CONFIGS.iter() {
            let d = rounds(n, k);
            let delta = scalars(1)[0];
            let (g, h, q, a, b, p_false) = statement(n, delta);
            for (round, _) in fold_pad_counts(n, k, d).iter().enumerate().filter(|&(_, &c)| c > 0) {
                let forged = forging_ipa(k, &g, &h, q, &a, &b, d, round, delta);
                assert!(!ipa_check(&forged, n, &g, &h, q, p_false));
            }
        }
    }
    #[test]
    fn honest_padded_ecp_proofs_verify() {
        for &(n, k) in CONFIGS.iter() {
            let d = rounds(n, k);
            for &c_len in [n, n - 2].iter() {
                let g = points(n);
                let c = points(c_len);
                let a = scalars(n);
                let p_g = msm(&a, &g);
                let p_c = msm(&a[..c_len], &c);
                let proof =
                    prove_ecp::<P>::create(&mut Transcript::new(b"ecp-test"), k, &g, &c, &a, d);
                assert!(ecp_check(&proof, n, &g, &c, p_g, p_c), "n={} k={} |C|={}", n, k, c_len);
                assert!(!ecp_check(&proof, n, &g, &c, p_g + g[0], p_c));
                assert!(!ecp_check(&proof, n, &g, &c, p_g, p_c + c[0]));
            }
        }
    }

    #[test]
    fn pad_generators_come_from_the_transcript() {
        let t = Transcript::new(b"pad-test");
        let mut t_other = Transcript::new(b"pad-test");
        t_other.append_message(b"x", b"1");
        let seed = pad_seed(&mut t.clone(), 1);
        assert_ne!(seed, pad_seed(&mut t.clone(), 2));
        assert_ne!(seed, pad_seed(&mut t_other, 1));

        let g_pad = fold_pad_generators::<P>(IPA_PAD_G_DOMAIN, &seed, 3);
        assert_eq!(g_pad, fold_pad_generators::<P>(IPA_PAD_G_DOMAIN, &seed, 3));
        assert!(g_pad.iter().all(|p| !p.is_zero()));
        for domain in [IPA_PAD_H_DOMAIN, ECP_PAD_G_DOMAIN].iter() {
            let other = fold_pad_generators::<P>(domain, &seed, 3);
            assert!(other.iter().all(|p| !g_pad.contains(p)));
        }
    }
    #[test]
    #[ignore]
    fn padding_generator_cost() {
        let configs = [
            (1_000usize, 2usize), (1_000, 4), (10_000, 2), (10_000, 4),
            (100_000, 2), (100_000, 4), (1_000_000, 2), (1_000_000, 4),
            (1_048_577, 2), (1_048_577, 4), (1_048_577, 5), (1_000_000, 16),
        ];
        println!();
        println!("{:>10} {:>3} {:>3} {:>6} {:>12} {:>12}",
                 "n", "k", "d", "gens", "derive(ms)", "msm(ms)");
        for &(n, k) in configs.iter() {
            let d = rounds(n, k);
            let counts = fold_pad_counts(n, k, d);
            let gens = counts.iter().sum::<usize>() * 3;
            let reps = 20;

            let start = Instant::now();
            for _ in 0..reps {
                let mut t = Transcript::new(b"pad-cost");
                for (r, &count) in counts.iter().enumerate() {
                    if count == 0 {
                        continue;
                    }
                    let seed = pad_seed(&mut t, r);
                    fold_pad_generators::<P>(IPA_PAD_G_DOMAIN, &seed, count);
                    fold_pad_generators::<P>(IPA_PAD_H_DOMAIN, &seed, count);
                    fold_pad_generators::<P>(ECP_PAD_G_DOMAIN, &seed, count);
                }
            }
            let derive = start.elapsed().as_secs_f64() * 1e3 / reps as f64;

            let pts = points(gens.max(1));
            let scs = scalars(gens.max(1));
            let start = Instant::now();
            for _ in 0..reps {
                let _ = msm(&scs, &pts);
            }
            let extra_msm = start.elapsed().as_secs_f64() * 1e3 / reps as f64;

            println!("{:>10} {:>3} {:>3} {:>6} {:>12.3} {:>12.3}",
                     n, k, d, gens, derive, extra_msm);
        }
    }

    #[test]
    fn malformed_encodings_are_rejected() {
        let headers = [
            (0u64, 1u64, 1u64),
            (1, 1, 1),
            (65, 1, 1),
            (u64::MAX, 1, 1),
            (4, 65, 1),
            (2, 1 << 40, 1),
            (4, 1, 0),
            (4, 1, u64::MAX),
            (4, 1, 1 << 60),
        ];
        for &(k, d, m) in headers.iter() {
            let mut buf = Vec::new();
            buf.extend_from_slice(&k.to_le_bytes());
            buf.extend_from_slice(&d.to_le_bytes());
            buf.extend_from_slice(&m.to_le_bytes());
            buf.extend(vec![0u8; 256]);
            assert!(prove_ipa::<P>::from_bytes(&buf).is_err());
            assert!(prove_ecp::<P>::from_bytes(&buf).is_err());
        }

        let (g, h, q) = (points(10), points(10), points(1)[0]);
        let proof = prove_ipa::<P>::create(
            &mut Transcript::new(b"ipa-test"), 4, &g, &h, q, &scalars(10), &scalars(10), 2,
        );
        let bytes = proof.to_bytes();
        assert!(prove_ipa::<P>::from_bytes(&bytes).is_ok());
        assert!(prove_ipa::<P>::from_bytes(&bytes[..bytes.len() - 1]).is_err());
        let mut longer = bytes.clone();
        longer.push(0);
        assert!(prove_ipa::<P>::from_bytes(&longer).is_err());

        let mut bad_k = proof.clone();
        bad_k.k = 0;
        assert!(bad_k.verification_scalars(10, &mut Transcript::new(b"ipa-test")).is_err());
        let mut bad_round = proof.clone();
        bad_round.U_vecs[0].pop();
        assert!(bad_round.verification_scalars(10, &mut Transcript::new(b"ipa-test")).is_err());
        assert!(proof.verification_scalars(0, &mut Transcript::new(b"ipa-test")).is_err());

        let ecp = prove_ecp::<P>::create(&mut Transcript::new(b"ecp-test"), 4, &g, &h, &scalars(10), 2);
        let ecp_bytes = ecp.to_bytes();
        assert!(prove_ecp::<P>::from_bytes(&ecp_bytes).is_ok());
        assert!(prove_ecp::<P>::from_bytes(&ecp_bytes[..ecp_bytes.len() - 1]).is_err());
        let mut bad_ecp = ecp.clone();
        bad_ecp.k = 1;
        assert!(bad_ecp.verification_scalars(10, &mut Transcript::new(b"ecp-test")).is_err());
    }
}