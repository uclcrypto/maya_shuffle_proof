#![allow(non_snake_case)]

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::VartimeMultiscalarMul;
use merlin::Transcript;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

use errors::ProofError;
use generators::fold_pad_generators;
use std::convert::TryInto;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Instant;
use transcript::TranscriptProtocol;

static IPP_TIMING_PRINTED: AtomicBool = AtomicBool::new(false);

pub(crate) const IPA_PAD_G_DOMAIN: &[u8] = b"MAYA-ipa-pad-g-v1";
pub(crate) const IPA_PAD_H_DOMAIN: &[u8] = b"MAYA-ipa-pad-h-v1";
pub(crate) const ECP_PAD_G_DOMAIN: &[u8] = b"MAYA-ecp-pad-G-v1";
pub(crate) const MAX_FOLD_FACTOR: usize = 64;
pub(crate) const MAX_FOLD_ROUNDS: usize = 64;

#[cfg(feature = "parallel")]
struct KnownSizeIter<I: Iterator> {
    inner: I,
    remaining: usize,
}
#[cfg(feature = "parallel")]
impl<I: Iterator> KnownSizeIter<I> {
    fn new(inner: I, size: usize) -> Self {
        Self {
            inner,
            remaining: size,
        }
    }
}
#[cfg(feature = "parallel")]
impl<I: Iterator> Iterator for KnownSizeIter<I> {
    type Item = I::Item;
    fn next(&mut self) -> Option<I::Item> {
        if self.remaining > 0 {
            self.remaining -= 1;
        }
        self.inner.next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}
#[cfg(feature = "parallel")]
impl<I: Iterator> ExactSizeIterator for KnownSizeIter<I> {}

fn scalar_pow(base: Scalar, mut exp: u64) -> Scalar {
    let mut result = Scalar::ONE;
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

//  prove_ipa (IPA with Iterative Padding)
#[derive(Clone, Debug)]
pub struct prove_ipa {
    pub(crate) k: usize,
    pub(crate) U_vecs: Vec<Vec<CompressedRistretto>>,
    pub(crate) a_final: Vec<Scalar>,
    pub(crate) b_final: Vec<Scalar>,
}

impl prove_ipa {
    pub fn create(
        transcript: &mut Transcript,
        k: usize,
        g_vec: &[RistrettoPoint],
        h_vec: &[RistrettoPoint],
        Q_point: RistrettoPoint,
        a_vec: &[Scalar],
        b_vec: &[Scalar],
        num_rounds: usize,
    ) -> prove_ipa {
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
        if _do_print {
            eprintln!("  [IPP] Starting prove_ipa::create (n={}, k={})", n, k);
        }

        let _t_phase: Instant = Instant::now();
        transcript.append_message(b"protocol-name", b"k_bullet_delay");
        transcript.append_message(b"n", &(n as u64).to_le_bytes());
        transcript.append_message(b"k", &(k as u64).to_le_bytes());

        let mut g_curr = g_vec.to_vec();
        let mut h_curr = h_vec.to_vec();
        let mut a_curr = a_vec.to_vec();
        let mut b_curr = b_vec.to_vec();

        let mut U_vecs: Vec<Vec<CompressedRistretto>> = Vec::with_capacity(num_rounds);

        let mut _scalars_l: Vec<Scalar> = Vec::with_capacity(2 * n);
        let mut _points_l: Vec<RistrettoPoint> = Vec::with_capacity(2 * n);
        let mut _scalars_neg_l: Vec<Scalar> = Vec::with_capacity(2 * n);
        let mut _points_neg_l: Vec<RistrettoPoint> = Vec::with_capacity(2 * n);

        let mut n_j = n;

        for j in 0..num_rounds {
           let _t_round = Instant::now();

            let rem = n_j % k;
            if rem != 0 {
                let pad = k - rem;
                a_curr.extend(std::iter::repeat(Scalar::ZERO).take(pad));
                b_curr.extend(std::iter::repeat(Scalar::ZERO).take(pad));
                let seed = pad_seed(transcript, j);
                g_curr.extend(fold_pad_generators(IPA_PAD_G_DOMAIN, &seed, pad));
                h_curr.extend(fold_pad_generators(IPA_PAD_H_DOMAIN, &seed, pad));
                n_j += pad;
            }

            let m_j = n_j / k;
            let _t_cross = Instant::now();

            let a_splits: Vec<&[Scalar]> = a_curr.chunks(m_j).collect();
            let b_splits: Vec<&[Scalar]> = b_curr.chunks(m_j).collect();
            let g_splits: Vec<&[RistrettoPoint]> = g_curr.chunks(m_j).collect();
            let h_splits: Vec<&[RistrettoPoint]> = h_curr.chunks(m_j).collect();

            #[cfg(feature = "parallel")]
            let (U_pos_compressed, U_neg_compressed) = {
                let results: Vec<(CompressedRistretto, CompressedRistretto)> = (1..k)
                    .into_par_iter()
                    .map(|l| {
                        let v_pos_l: Scalar = (0..(k - l))
                            .map(|i| inner_product(a_splits[i], b_splits[i + l]))
                            .sum();
                        let v_neg_l: Scalar = (0..(k - l))
                            .map(|i| inner_product(a_splits[i + l], b_splits[i]))
                            .sum();

                        let sz = (k - l) * 2 * m_j;
                        let sc_pos = KnownSizeIter::new(
                            (0..(k - l))
                                .flat_map(|i| a_splits[i].iter().chain(b_splits[i + l].iter())),
                            sz,
                        );
                        let pt_pos = KnownSizeIter::new(
                            (0..(k - l))
                                .flat_map(|i| g_splits[i + l].iter().chain(h_splits[i].iter())),
                            sz,
                        );
                        let sc_neg = KnownSizeIter::new(
                            (0..(k - l))
                                .flat_map(|i| a_splits[i + l].iter().chain(b_splits[i].iter())),
                            sz,
                        );
                        let pt_neg = KnownSizeIter::new(
                            (0..(k - l))
                                .flat_map(|i| g_splits[i].iter().chain(h_splits[i + l].iter())),
                            sz,
                        );

                        let (U_l, U_neg_l) = rayon::join(
                            || {
                                RistrettoPoint::vartime_multiscalar_mul(sc_pos, pt_pos)
                                    + v_pos_l * Q_point
                            },
                            || {
                                RistrettoPoint::vartime_multiscalar_mul(sc_neg, pt_neg)
                                    + v_neg_l * Q_point
                            },
                        );
                        (U_l.compress(), U_neg_l.compress())
                    })
                    .collect();
                let mut pos = Vec::with_capacity(k - 1);
                let mut neg = Vec::with_capacity(k - 1);
                for (p, n) in results {
                    pos.push(p);
                    neg.push(n);
                }
                (pos, neg)
            };
            #[cfg(not(feature = "parallel"))]
            let (U_pos_compressed, U_neg_compressed) = {
                let mut pos = Vec::with_capacity(k - 1);
                let mut neg = Vec::with_capacity(k - 1);
                for l in 1..k {
                    let mut v_pos_l = Scalar::ZERO;
                    let mut v_neg_l = Scalar::ZERO;
                    _scalars_l.clear();
                    _points_l.clear();
                    _scalars_neg_l.clear();
                    _points_neg_l.clear();
                    for i in 0..(k - l) {
                        v_pos_l += inner_product(a_splits[i], b_splits[i + l]);
                        _scalars_l.extend_from_slice(a_splits[i]);
                        _points_l.extend_from_slice(g_splits[i + l]);
                        _scalars_l.extend_from_slice(b_splits[i + l]);
                        _points_l.extend_from_slice(h_splits[i]);
                        v_neg_l += inner_product(a_splits[i + l], b_splits[i]);
                        _scalars_neg_l.extend_from_slice(a_splits[i + l]);
                        _points_neg_l.extend_from_slice(g_splits[i]);
                        _scalars_neg_l.extend_from_slice(b_splits[i]);
                        _points_neg_l.extend_from_slice(h_splits[i + l]);
                    }
                    let U_l = RistrettoPoint::vartime_multiscalar_mul(
                        _scalars_l.iter(),
                        _points_l.iter(),
                    ) + v_pos_l * Q_point;
                    let U_neg_l = RistrettoPoint::vartime_multiscalar_mul(
                        _scalars_neg_l.iter(),
                        _points_neg_l.iter(),
                    ) + v_neg_l * Q_point;
                    pos.push(U_l.compress());
                    neg.push(U_neg_l.compress());
                }
                (pos, neg)
            };

            let _t_transcript = Instant::now();
            let mut U_vec_round = U_pos_compressed;
            U_vec_round.extend(U_neg_compressed);

            for (idx, point_compressed) in U_vec_round.iter().enumerate() {
                transcript.append_message(b"U_round", &(j as u64).to_le_bytes());
                transcript.append_message(b"U_index", &(idx as u64).to_le_bytes());
                transcript.commit_point(b"U_point", &point_compressed);
            }
            U_vecs.push(U_vec_round);

            transcript.append_message(b"challenge_prefix", b"c_");
            transcript.append_message(b"challenge_index", &(j as u64).to_le_bytes());
            let c = transcript.challenge_scalar(b"challenge_separator");
            let c_inv = c.invert();

            let _t_wit = Instant::now();

            let mut a_new = vec![Scalar::ZERO; m_j];
            let mut b_new = vec![Scalar::ZERO; m_j];
            let mut g_new = vec![RistrettoPoint::default(); m_j];
            let mut h_new = vec![RistrettoPoint::default(); m_j];

            let mut c_powers_a: Vec<Scalar> = Vec::with_capacity(k);
            let mut c_pow_y = Scalar::ONE;
            for _ in 0..k {
                c_powers_a.push(c_pow_y);
                c_pow_y *= c;
            }

            let mut c_powers_b: Vec<Scalar> = Vec::with_capacity(k);
            let mut c_pow_x = Scalar::ONE;
            for _ in 1..k {
                c_pow_x *= c;
            }
            for _ in 0..k {
                c_powers_b.push(c_pow_x);
                c_pow_x *= c_inv;
            }

            let g_scalars = &c_powers_b;
            let h_scalars = &c_powers_a;

            let _t_wit = Instant::now();
            #[cfg(feature = "parallel")]
            {
                a_new
                    .par_iter_mut()
                    .zip(b_new.par_iter_mut())
                    .zip(g_new.par_iter_mut())
                    .zip(h_new.par_iter_mut())
                    .enumerate()
                    .for_each(|(j_item, (((a_out, b_out), g_out), h_out))| {
                        let mut a_j_acc = Scalar::ZERO;
                        let mut b_j_acc = Scalar::ZERO;
                        let g_col: Vec<RistrettoPoint> =
                            (0..k).map(|i| g_splits[i][j_item]).collect();
                        let h_col: Vec<RistrettoPoint> =
                            (0..k).map(|i| h_splits[i][j_item]).collect();
                        for i in 0..k {
                            a_j_acc += a_splits[i][j_item] * c_powers_a[i];
                            b_j_acc += b_splits[i][j_item] * c_powers_b[i];
                        }
                        *a_out = a_j_acc;
                        *b_out = b_j_acc;
                        *g_out =
                            RistrettoPoint::vartime_multiscalar_mul(g_scalars.iter(), g_col.iter());
                        *h_out =
                            RistrettoPoint::vartime_multiscalar_mul(h_scalars.iter(), h_col.iter());
                    });
            }
            #[cfg(not(feature = "parallel"))]
            {
                let mut g_points_col: Vec<RistrettoPoint> = vec![RistrettoPoint::default(); k];
                let mut h_points_col: Vec<RistrettoPoint> = vec![RistrettoPoint::default(); k];
                for j_item in 0..m_j {
                    let mut a_j_acc = Scalar::ZERO;
                    let mut b_j_acc = Scalar::ZERO;
                    for i in 0..k {
                        a_j_acc += a_splits[i][j_item] * c_powers_a[i];
                        b_j_acc += b_splits[i][j_item] * c_powers_b[i];
                        g_points_col[i] = g_splits[i][j_item];
                        h_points_col[i] = h_splits[i][j_item];
                    }
                    a_new[j_item] = a_j_acc;
                    b_new[j_item] = b_j_acc;
                    g_new[j_item] = RistrettoPoint::vartime_multiscalar_mul(
                        g_scalars.iter(),
                        g_points_col.iter(),
                    );
                    h_new[j_item] = RistrettoPoint::vartime_multiscalar_mul(
                        h_scalars.iter(),
                        h_points_col.iter(),
                    );
                }
            }

            a_curr = a_new;
            b_curr = b_new;
            g_curr = g_new;
            h_curr = h_new;

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
            Vec<Scalar>,
            Vec<Scalar>,
            Scalar,
            Scalar,
            Vec<Scalar>,
            Vec<Scalar>,
            Vec<RistrettoPoint>,
        ),
        ProofError,
    > {
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

        let mut challenges: Vec<Scalar> = Vec::with_capacity(d);
        let mut pad_points: Vec<RistrettoPoint> = Vec::new();
        let mut h_pad_points: Vec<RistrettoPoint> = Vec::new();

        for r in 0..d {
            let pad = round_lengths[r + 1] * k - round_lengths[r];
            if pad > 0 {
                let seed = pad_seed(transcript, r);
                pad_points.extend(fold_pad_generators(IPA_PAD_G_DOMAIN, &seed, pad));
                h_pad_points.extend(fold_pad_generators(IPA_PAD_H_DOMAIN, &seed, pad));
            }
            for i_list in 0..(2 * k - 2) {
                transcript.append_message(b"U_round", &(r as u64).to_le_bytes());
                transcript.append_message(b"U_index", &(i_list as u64).to_le_bytes());
                transcript.commit_point(b"U_point", &self.U_vecs[r][i_list]);
            }
            transcript.append_message(b"challenge_prefix", b"c_");
            transcript.append_message(b"challenge_index", &(r as u64).to_le_bytes());
            challenges.push(transcript.challenge_scalar(b"challenge_separator"));
        }

        let mut challenges_inv = challenges.clone();
        Scalar::batch_invert(&mut challenges_inv);

        let k_minus_1_exp = (k - 1) as u64;
        let mut c_k_minus_1_products = vec![Scalar::ONE; d];
        let mut product_so_far = Scalar::ONE;
        for r in (0..d).rev() {
            let c_k_minus_1 = scalar_pow(challenges[r], k_minus_1_exp);
            c_k_minus_1_products[r] = product_so_far;
            product_so_far *= c_k_minus_1;
        }
        let s_P = product_so_far;

        let mut s_g_pad_rounds: Vec<Vec<Scalar>> = vec![Vec::new(); d];
        let mut s_h_pad_rounds: Vec<Vec<Scalar>> = vec![Vec::new(); d];

        let mut s_g_full = self.a_final.clone();
        for r in (0..d).rev() {
            let c_inv = challenges_inv[r];
            let mut block = Vec::with_capacity(k);
            let mut val = Scalar::ONE;
            for _ in 0..k {
                block.push(val);
                val *= c_inv;
            }

            let mut next_s = Vec::with_capacity(s_g_full.len() * k);
            for b in block.iter() {
                for val in s_g_full.iter() {
                    next_s.push(val * b);
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
            let mut val = Scalar::ONE;
            for _ in 0..k {
                block.push(val);
                val *= c;
            }

            let mut next_s = Vec::with_capacity(s_h_full.len() * k);
            for b in block.iter() {
                for val in s_h_full.iter() {
                    next_s.push(val * b);
                }
            }

            s_h_pad_rounds[r] = next_s.split_off(round_lengths[r]);
            s_h_full = next_s;
        }

        let s_Q_final = inner_product(&self.a_final, &self.b_final);

        let mut s_U: Vec<Scalar> = Vec::with_capacity(d * (2 * k - 2));
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

        let mut s_pad: Vec<Scalar> = Vec::with_capacity(2 * pad_points.len());
        for r in 0..d {
            let factor = c_k_minus_1_products[r] * scalar_pow(challenges[r], k_minus_1_exp);
            s_pad.extend(s_g_pad_rounds[r].iter().map(|x| x * factor));
        }
        s_pad.extend(s_h_pad_rounds.into_iter().flatten());
        pad_points.extend(h_pad_points);

        Ok((s_g_full, s_h_full, s_Q_final, s_P, s_U, s_pad, pad_points))
    }

    pub fn serialized_size(&self) -> usize {
        let d = self.U_vecs.len();
        let num_points = if d > 0 { d * (2 * self.k - 2) } else { 0 };
        let m = self.a_final.len();
        (3 + num_points + 2 * m) * 32
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(self.serialized_size());
        let mut temp = [0u8; 32];
        temp[..8].copy_from_slice(&(self.k as u64).to_le_bytes());
        buf.extend_from_slice(&temp);

        let d = self.U_vecs.len();
        temp = [0u8; 32];
        temp[..8].copy_from_slice(&(d as u64).to_le_bytes());
        buf.extend_from_slice(&temp);

        let m = self.a_final.len();
        temp = [0u8; 32];
        temp[..8].copy_from_slice(&(m as u64).to_le_bytes());
        buf.extend_from_slice(&temp);

        for round_vec in self.U_vecs.iter() {
            for point in round_vec.iter() {
                buf.extend_from_slice(point.as_bytes());
            }
        }
        for x in &self.a_final {
            buf.extend_from_slice(x.as_bytes());
        }
        for x in &self.b_final {
            buf.extend_from_slice(x.as_bytes());
        }
        buf
    }

    pub fn from_bytes(slice: &[u8]) -> Result<prove_ipa, ProofError> {
        let b = slice.len();
        if b < 32 * 3 {
            return Err(ProofError::FormatError);
        }
        use util::read32;
        let mut pos = 0;

        let k_bytes = read32(&slice[pos..]);
        let k = u64::from_le_bytes(k_bytes[..8].try_into().unwrap()) as usize;
        pos += 32;
        let d_bytes = read32(&slice[pos..]);
        let d = u64::from_le_bytes(d_bytes[..8].try_into().unwrap()) as usize;
        pos += 32;
        let m_bytes = read32(&slice[pos..]);
        let m = u64::from_le_bytes(m_bytes[..8].try_into().unwrap()) as usize;
        pos += 32;

        if k < 2
            || k > MAX_FOLD_FACTOR
            || d > MAX_FOLD_ROUNDS
            || m == 0
            || k_bytes[8..].iter().chain(&d_bytes[8..]).chain(&m_bytes[8..]).any(|&x| x != 0)
        {
            return Err(ProofError::FormatError);
        }
        let expected_len = m
            .checked_mul(2)
            .and_then(|s| s.checked_add(d * (2 * k - 2)))
            .and_then(|w| w.checked_add(3))
            .and_then(|w| w.checked_mul(32))
            .ok_or(ProofError::FormatError)?;
        if b != expected_len {
            return Err(ProofError::FormatError);
        }

        let points_per_round = 2 * k - 2;
        let mut U_vecs = Vec::with_capacity(d);
        for _ in 0..d {
            let mut round = Vec::with_capacity(points_per_round);
            for _ in 0..points_per_round {
                if pos + 32 > b {
                    return Err(ProofError::FormatError);
                }
                round.push(CompressedRistretto(read32(&slice[pos..])));
                pos += 32;
            }
            U_vecs.push(round);
        }

        let mut a_final = Vec::with_capacity(m);
        for _ in 0..m {
            if pos + 32 > b {
                return Err(ProofError::FormatError);
            }
            let s = Option::from(Scalar::from_canonical_bytes(read32(&slice[pos..])))
                .ok_or(ProofError::FormatError)?;
            a_final.push(s);
            pos += 32;
        }

        let mut b_final = Vec::with_capacity(m);
        for _ in 0..m {
            if pos + 32 > b {
                return Err(ProofError::FormatError);
            }
            let s = Option::from(Scalar::from_canonical_bytes(read32(&slice[pos..])))
                .ok_or(ProofError::FormatError)?;
            b_final.push(s);
            pos += 32;
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
pub struct prove_ecp {
    pub(crate) k: usize,
    pub(crate) A_vecs: Vec<Vec<[CompressedRistretto; 2]>>,
    pub(crate) z: Vec<Scalar>,
}

impl prove_ecp {
    pub fn create(
        transcript: &mut Transcript,
        k: usize,
        G_vec: &[RistrettoPoint],
        C1_vec: &[RistrettoPoint],
        a_vec: &[Scalar],
        num_rounds: usize,
    ) -> prove_ecp {
        let n = a_vec.len();

        let mut a_curr = a_vec.to_vec();
        let mut G_curr = G_vec.to_vec();
        let mut C1_curr = C1_vec.to_vec();

        if C1_curr.len() < n {
            C1_curr.resize(n, RistrettoPoint::default());
        }

        transcript.append_message(b"protocol-name", b"k_ipp_delay_2");
        transcript.append_message(b"n", &(n as u64).to_le_bytes());
        transcript.append_message(b"k", &(k as u64).to_le_bytes());

        let mut A_vecs: Vec<Vec<[CompressedRistretto; 2]>> = Vec::with_capacity(num_rounds);

        let mut _scalars_0: Vec<Scalar> = Vec::with_capacity(n);
        let mut _points_0: Vec<RistrettoPoint> = Vec::with_capacity(n);
        let mut _scalars_1: Vec<Scalar> = Vec::with_capacity(n);
        let mut _points_1: Vec<RistrettoPoint> = Vec::with_capacity(n);

        let mut _ecp_t_cross = std::time::Duration::ZERO;
        let mut _ecp_t_fold_w = std::time::Duration::ZERO;

        let mut n_j = n;

        for round_idx in 0..num_rounds {
            let rem = n_j % k;
            if rem != 0 {
                let pad = k - rem;
                a_curr.extend(std::iter::repeat(Scalar::ZERO).take(pad));
                let seed = pad_seed(transcript, round_idx);
                G_curr.extend(fold_pad_generators(ECP_PAD_G_DOMAIN, &seed, pad));
                C1_curr.extend(std::iter::repeat(RistrettoPoint::default()).take(pad));
                n_j += pad;
            }

            let m_j = n_j / k;

            let a_splits: Vec<&[Scalar]> = a_curr.chunks(m_j).collect();
            let G_splits: Vec<&[RistrettoPoint]> = G_curr.chunks(m_j).collect();
            let C1_splits: Vec<&[RistrettoPoint]> = C1_curr.chunks(m_j).collect();

            let mut A_vecs_round: Vec<[CompressedRistretto; 2]> = Vec::with_capacity(2 * k - 2);
            let mut A_points_round: Vec<[RistrettoPoint; 2]> = Vec::with_capacity(2 * k - 2);

            let _tc = Instant::now();
            #[cfg(feature = "parallel")]
            {
                let results: Vec<[RistrettoPoint; 2]> = (0..2 * (k - 1))
                    .into_par_iter()
                    .map(|idx| {
                        if idx < k - 1 {
                            let i = idx + 1;
                            let sz = i * m_j;
                            let sc_g = KnownSizeIter::new(
                                (1..(i + 1)).flat_map(|l| a_splits[l - 1].iter()),
                                sz,
                            );
                            let sc_c1 = KnownSizeIter::new(
                                (1..(i + 1)).flat_map(|l| a_splits[l - 1].iter()),
                                sz,
                            );
                            let pt_g = KnownSizeIter::new(
                                (1..(i + 1)).flat_map(|l| G_splits[k - i + l - 1].iter()),
                                sz,
                            );
                            let pt_c1 = KnownSizeIter::new(
                                (1..(i + 1)).flat_map(|l| C1_splits[k - i + l - 1].iter()),
                                sz,
                            );
                            let (p0, p1) = rayon::join(
                                || RistrettoPoint::vartime_multiscalar_mul(sc_g, pt_g),
                                || RistrettoPoint::vartime_multiscalar_mul(sc_c1, pt_c1),
                            );
                            [p0, p1]
                        } else {
                            let i = idx - (k - 2);
                            let sz = (k - i) * m_j;
                            let sc_g = KnownSizeIter::new(
                                (1..(k - i + 1)).flat_map(|l| a_splits[i + l - 1].iter()),
                                sz,
                            );
                            let sc_c1 = KnownSizeIter::new(
                                (1..(k - i + 1)).flat_map(|l| a_splits[i + l - 1].iter()),
                                sz,
                            );
                            let pt_g = KnownSizeIter::new(
                                (1..(k - i + 1)).flat_map(|l| G_splits[l - 1].iter()),
                                sz,
                            );
                            let pt_c1 = KnownSizeIter::new(
                                (1..(k - i + 1)).flat_map(|l| C1_splits[l - 1].iter()),
                                sz,
                            );
                            let (p0, p1) = rayon::join(
                                || RistrettoPoint::vartime_multiscalar_mul(sc_g, pt_g),
                                || RistrettoPoint::vartime_multiscalar_mul(sc_c1, pt_c1),
                            );
                            [p0, p1]
                        }
                    })
                    .collect();
                A_points_round.extend(results);
            }
            #[cfg(not(feature = "parallel"))]
            {
                for i in 1..k {
                    _scalars_0.clear();
                    _points_0.clear();
                    _scalars_1.clear();
                    _points_1.clear();
                    for l in 1..(i + 1) {
                        _scalars_0.extend_from_slice(a_splits[l - 1]);
                        _points_0.extend_from_slice(G_splits[k - i + l - 1]);
                        _scalars_1.extend_from_slice(a_splits[l - 1]);
                        _points_1.extend_from_slice(C1_splits[k - i + l - 1]);
                    }
                    let p0 = RistrettoPoint::vartime_multiscalar_mul(
                        _scalars_0.iter(),
                        _points_0.iter(),
                    );
                    let p1 = RistrettoPoint::vartime_multiscalar_mul(
                        _scalars_1.iter(),
                        _points_1.iter(),
                    );
                    A_points_round.push([p0, p1]);
                }
                for i in 1..k {
                    _scalars_0.clear();
                    _points_0.clear();
                    _scalars_1.clear();
                    _points_1.clear();
                    for l in 1..(k - i + 1) {
                        _scalars_0.extend_from_slice(a_splits[i + l - 1]);
                        _points_0.extend_from_slice(G_splits[l - 1]);
                        _scalars_1.extend_from_slice(a_splits[i + l - 1]);
                        _points_1.extend_from_slice(C1_splits[l - 1]);
                    }
                    let p0 = RistrettoPoint::vartime_multiscalar_mul(
                        _scalars_0.iter(),
                        _points_0.iter(),
                    );
                    let p1 = RistrettoPoint::vartime_multiscalar_mul(
                        _scalars_1.iter(),
                        _points_1.iter(),
                    );
                    A_points_round.push([p0, p1]);
                }
            }
            _ecp_t_cross += _tc.elapsed();

            for (idx, points_tuple) in A_points_round.iter().enumerate() {
                let compressed_tuple = [points_tuple[0].compress(), points_tuple[1].compress()];
                A_vecs_round.push(compressed_tuple);

                transcript.append_message(b"A_round", &(round_idx as u64).to_le_bytes());
                transcript.append_message(b"A_index", &(idx as u64).to_le_bytes());
                transcript.commit_point(b"A_point_0", &compressed_tuple[0]);
                transcript.commit_point(b"A_point_1", &compressed_tuple[1]);
            }
            A_vecs.push(A_vecs_round);

            transcript.append_message(b"challenge_prefix", b"c_");
            transcript.append_message(b"challenge_index", &(round_idx as u64).to_le_bytes());
            let c = transcript.challenge_scalar(b"challenge_separator");

            let mut a_new = vec![Scalar::ZERO; m_j];
            let mut G_new = vec![RistrettoPoint::default(); m_j];
            let mut C1_new = vec![RistrettoPoint::default(); m_j];

            let mut c_powers_a: Vec<Scalar> = Vec::with_capacity(k);
            let mut c_pow = Scalar::ONE;
            for _ in 0..k {
                c_powers_a.push(c_pow);
                c_pow *= c;
            }

            let c_inv = c.invert();
            let mut c_powers_bases = Vec::with_capacity(k);
            let mut c_pow_exp = scalar_pow(c, k as u64);
            for _ in 0..k {
                c_powers_bases.push(c_pow_exp);
                c_pow_exp *= c_inv;
            }

            let _tw = Instant::now();
            #[cfg(feature = "parallel")]
            {
                a_new
                    .par_iter_mut()
                    .zip(G_new.par_iter_mut())
                    .zip(C1_new.par_iter_mut())
                    .enumerate()
                    .for_each(|(j_item, ((a_out, g_out), c1_out))| {
                        let mut a_acc = Scalar::ZERO;
                        let g_col: Vec<RistrettoPoint> =
                            (0..k).map(|i| G_splits[i][j_item]).collect();
                        let c1_col: Vec<RistrettoPoint> =
                            (0..k).map(|i| C1_splits[i][j_item]).collect();
                        for i in 0..k {
                            a_acc += a_splits[i][j_item] * c_powers_a[i];
                        }
                        *a_out = a_acc;
                        *g_out = RistrettoPoint::vartime_multiscalar_mul(
                            c_powers_bases.iter(),
                            g_col.iter(),
                        );
                        *c1_out = RistrettoPoint::vartime_multiscalar_mul(
                            c_powers_bases.iter(),
                            c1_col.iter(),
                        );
                    });
            }
            #[cfg(not(feature = "parallel"))]
            {
                let mut g_col = vec![RistrettoPoint::default(); k];
                let mut c1_col = vec![RistrettoPoint::default(); k];
                for j_item in 0..m_j {
                    let mut a_acc = Scalar::ZERO;
                    for i in 0..k {
                        a_acc += a_splits[i][j_item] * c_powers_a[i];
                        g_col[i] = G_splits[i][j_item];
                        c1_col[i] = C1_splits[i][j_item];
                    }
                    a_new[j_item] = a_acc;
                    G_new[j_item] = RistrettoPoint::vartime_multiscalar_mul(
                        c_powers_bases.iter(),
                        g_col.iter(),
                    );
                    C1_new[j_item] = RistrettoPoint::vartime_multiscalar_mul(
                        c_powers_bases.iter(),
                        c1_col.iter(),
                    );
                }
            }
            _ecp_t_fold_w += _tw.elapsed();

            a_curr = a_new;
            G_curr = G_new;
            C1_curr = C1_new;
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
    ) -> Result<(Vec<Scalar>, Scalar, Vec<Scalar>, Vec<Scalar>, Vec<RistrettoPoint>), ProofError> {
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

        let mut challenges: Vec<Scalar> = Vec::with_capacity(d);
        let mut pad_points: Vec<RistrettoPoint> = Vec::new();
        for r in 0..d {
            let pad = round_lengths[r + 1] * k - round_lengths[r];
            if pad > 0 {
                let seed = pad_seed(transcript, r);
                pad_points.extend(fold_pad_generators(ECP_PAD_G_DOMAIN, &seed, pad));
            }
            for i_list in 0..(2 * k - 2) {
                let tuple = self.A_vecs[r][i_list];
                transcript.append_message(b"A_round", &(r as u64).to_le_bytes());
                transcript.append_message(b"A_index", &(i_list as u64).to_le_bytes());
                transcript.commit_point(b"A_point_0", &tuple[0]);
                transcript.commit_point(b"A_point_1", &tuple[1]);
            }
            transcript.append_message(b"challenge_prefix", b"c_");
            transcript.append_message(b"challenge_index", &(r as u64).to_le_bytes());
            challenges.push(transcript.challenge_scalar(b"challenge_separator"));
        }

        let mut challenges_inv = challenges.clone();
        Scalar::batch_invert(&mut challenges_inv);

        let k_exp = k as u64;
        let mut c_k_products = vec![Scalar::ONE; d];
        let mut product_so_far = Scalar::ONE;
        for r in (0..d).rev() {
            let c_k = scalar_pow(challenges[r], k_exp);
            c_k_products[r] = product_so_far;
            product_so_far *= c_k;
        }
        let s_P = product_so_far;

        let mut z_s_pad_rounds: Vec<Vec<Scalar>> = vec![Vec::new(); d];

        let mut z_s_vec = self.z.clone();
        for r in (0..d).rev() {
            let c_inv = challenges_inv[r];
            let mut block = Vec::with_capacity(k);
            let mut val = Scalar::ONE;
            for _ in 0..k {
                block.push(val);
                val *= c_inv;
            }

            let mut next_s = Vec::with_capacity(z_s_vec.len() * k);
            for b in block.iter() {
                for z_val in z_s_vec.iter() {
                    next_s.push(z_val * b);
                }
            }

            z_s_pad_rounds[r] = next_s.split_off(round_lengths[r]);
            z_s_vec = next_s;
        }

        for x in z_s_vec.iter_mut() {
            *x *= s_P;
        }

        let mut s_A_vec: Vec<Scalar> = Vec::with_capacity(d * (2 * k - 2));
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

        let mut z_s_pad: Vec<Scalar> = Vec::new();
        for r in 0..d {
            let factor = c_k_products[r] * scalar_pow(challenges[r], k_exp);
            z_s_pad.extend(z_s_pad_rounds[r].iter().map(|x| x * factor));
        }

        Ok((z_s_vec, s_P, s_A_vec, z_s_pad, pad_points))
    }

    pub fn serialized_size(&self) -> usize {
        let d = self.A_vecs.len();
        let mut num_points = 0;
        if d > 0 {
            num_points = d * (2 * self.k - 2) * 2;
        }
        let m = self.z.len();
        (3 + num_points + m) * 32
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(self.serialized_size());
        let mut temp = [0u8; 32];
        temp[..8].copy_from_slice(&(self.k as u64).to_le_bytes());
        buf.extend_from_slice(&temp);

        let d = self.A_vecs.len();
        temp = [0u8; 32];
        temp[..8].copy_from_slice(&(d as u64).to_le_bytes());
        buf.extend_from_slice(&temp);

        let m = self.z.len();
        temp = [0u8; 32];
        temp[..8].copy_from_slice(&(m as u64).to_le_bytes());
        buf.extend_from_slice(&temp);

        for round_vec in self.A_vecs.iter() {
            for point_tuple in round_vec.iter() {
                buf.extend_from_slice(point_tuple[0].as_bytes());
                buf.extend_from_slice(point_tuple[1].as_bytes());
            }
        }
        for s in &self.z {
            buf.extend_from_slice(s.as_bytes());
        }
        buf
    }

    pub fn from_bytes(slice: &[u8]) -> Result<prove_ecp, ProofError> {
        let b = slice.len();
        if b < 32 * 3 {
            return Err(ProofError::FormatError);
        }
        use util::read32;
        let mut pos = 0;
        let k_bytes = read32(&slice[pos..]);
        let k = u64::from_le_bytes(k_bytes[..8].try_into().unwrap()) as usize;
        pos += 32;
        let d_bytes = read32(&slice[pos..]);
        let d = u64::from_le_bytes(d_bytes[..8].try_into().unwrap()) as usize;
        pos += 32;
        let m_bytes = read32(&slice[pos..]);
        let m = u64::from_le_bytes(m_bytes[..8].try_into().unwrap()) as usize;
        pos += 32;

        if k < 2
            || k > MAX_FOLD_FACTOR
            || d > MAX_FOLD_ROUNDS
            || m == 0
            || k_bytes[8..].iter().chain(&d_bytes[8..]).chain(&m_bytes[8..]).any(|&x| x != 0)
        {
            return Err(ProofError::FormatError);
        }
        let expected_len = m
            .checked_add(d * (4 * k - 4))
            .and_then(|w| w.checked_add(3))
            .and_then(|w| w.checked_mul(32))
            .ok_or(ProofError::FormatError)?;
        if b != expected_len {
            return Err(ProofError::FormatError);
        }

        let mut A_vecs = Vec::with_capacity(d);
        for _ in 0..d {
            let mut round = Vec::with_capacity(2 * k - 2);
            for _ in 0..(2 * k - 2) {
                if pos + 64 > b {
                    return Err(ProofError::FormatError);
                }
                let p0 = CompressedRistretto(read32(&slice[pos..]));
                pos += 32;
                let p1 = CompressedRistretto(read32(&slice[pos..]));
                pos += 32;
                round.push([p0, p1]);
            }
            A_vecs.push(round);
        }
        let mut z = Vec::with_capacity(m);
        for _ in 0..m {
            if pos + 32 > b {
                return Err(ProofError::FormatError);
            }
            let s = Option::from(Scalar::from_canonical_bytes(read32(&slice[pos..])))
                .ok_or(ProofError::FormatError)?;
            z.push(s);
            pos += 32;
        }
        Ok(prove_ecp { k, A_vecs, z })
    }
}

pub fn inner_product(a: &[Scalar], b: &[Scalar]) -> Scalar {
    let mut out = Scalar::ZERO;
    if a.len() != b.len() {
        panic!("inner_product(a,b): lengths of vectors do not match");
    }
    for i in 0..a.len() {
        out += a[i] * b[i];
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn points(n: usize) -> Vec<RistrettoPoint> {
        let mut rng = rand::thread_rng();
        (0..n).map(|_| RistrettoPoint::random(&mut rng)).collect()
    }

    fn scalars(n: usize) -> Vec<Scalar> {
        let mut rng = rand::thread_rng();
        (0..n).map(|_| Scalar::random(&mut rng)).collect()
    }

    fn msm(s: &[Scalar], p: &[RistrettoPoint]) -> RistrettoPoint {
        RistrettoPoint::vartime_multiscalar_mul(s.iter(), p.iter())
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
        k: usize, g_vec: &[RistrettoPoint], h_vec: &[RistrettoPoint], q: RistrettoPoint,
        a_vec: &[Scalar], b_vec: &[Scalar], num_rounds: usize, round: usize, delta: Scalar,
    ) -> prove_ipa {
        let transcript = &mut Transcript::new(b"ipa-test");
        let n = a_vec.len();
        transcript.append_message(b"protocol-name", b"k_bullet_delay");
        transcript.append_message(b"n", &(n as u64).to_le_bytes());
        transcript.append_message(b"k", &(k as u64).to_le_bytes());
        
        let counts = fold_pad_counts(n, k, num_rounds);
        let (mut g, mut h) = (g_vec.to_vec(), h_vec.to_vec());
        let (mut a, mut b) = (a_vec.to_vec(), b_vec.to_vec());
        
        let mut gap = delta;
        
        let mut U_vecs = Vec::with_capacity(num_rounds);
        
        for j in 0..num_rounds {
            if counts[j] > 0 {
                let start = a.len();
                a.extend(std::iter::repeat(Scalar::ZERO).take(counts[j]));
                b.extend(std::iter::repeat(Scalar::ZERO).take(counts[j]));
                let seed = pad_seed(transcript, j);
                g.extend(fold_pad_generators(IPA_PAD_G_DOMAIN, &seed, counts[j]));
                h.extend(fold_pad_generators(IPA_PAD_H_DOMAIN, &seed, counts[j]));
                
                if round == j {
                    a[start] = gap; b[start] = Scalar::ONE; gap = Scalar::ZERO;
                }
            }
            
            let m = a.len() / k;
            let (a_s, b_s): (Vec<&[Scalar]>, Vec<&[Scalar]>) = (a.chunks(m).collect(), b.chunks(m).collect());
            let (g_s, h_s): (Vec<&[RistrettoPoint]>, Vec<&[RistrettoPoint]>) = (g.chunks(m).collect(), h.chunks(m).collect());
            let (mut pos, mut neg) = (Vec::with_capacity(k - 1), Vec::with_capacity(k - 1));
            
            for l in 1..k {
                let (mut u_pos, mut u_neg) = (RistrettoPoint::default(), RistrettoPoint::default());
                for i in 0..(k - l) {
                    u_pos += msm(a_s[i], g_s[i + l]) + msm(b_s[i + l], h_s[i]) + inner_product(a_s[i], b_s[i + l]) * q;
                    u_neg += msm(a_s[i + l], g_s[i]) + msm(b_s[i], h_s[i + l]) + inner_product(a_s[i + l], b_s[i]) * q;
                }
                pos.push(u_pos); neg.push(u_neg);
            }
            
            
            
            let mut round_points: Vec<CompressedRistretto> = pos.iter().map(|p| p.compress()).collect();
            round_points.extend(neg.iter().map(|p| p.compress()));
            for (idx, point) in round_points.iter().enumerate() {
                transcript.append_message(b"U_round", &(j as u64).to_le_bytes());
                transcript.append_message(b"U_index", &(idx as u64).to_le_bytes());
                transcript.commit_point(b"U_point", point);
            }
            U_vecs.push(round_points);
            
            transcript.append_message(b"challenge_prefix", b"c_");
            transcript.append_message(b"challenge_index", &(j as u64).to_le_bytes());
            let c = transcript.challenge_scalar(b"challenge_separator");
            let c_inv = c.invert();
            
            let (mut a_new, mut b_new) = (vec![Scalar::ZERO; m], vec![Scalar::ZERO; m]);
            let (mut g_new, mut h_new) = (vec![RistrettoPoint::default(); m], vec![RistrettoPoint::default(); m]);
            
            for i in 0..k {
                let c_i = scalar_pow(c, i as u64);
                let c_rev = scalar_pow(c, (k - 1) as u64) * scalar_pow(c_inv, i as u64);
                for t in 0..m {
                    a_new[t] += a_s[i][t] * c_i; b_new[t] += b_s[i][t] * c_rev;
                    g_new[t] += g_s[i][t] * c_rev; h_new[t] += h_s[i][t] * c_i;
                }
            }
            a = a_new; b = b_new; g = g_new; h = h_new; gap *= scalar_pow(c, (k - 1) as u64);
        }
        
        prove_ipa { k, U_vecs, a_final: a, b_final: b }
    }

    fn ipa_check(proof: &prove_ipa, n: usize, g: &[RistrettoPoint], h: &[RistrettoPoint], q: RistrettoPoint, p: RistrettoPoint) -> bool {
        let mut transcript = Transcript::new(b"ipa-test");
        let (s_g, s_h, s_q, s_p, s_u, s_pad, pad_points) = match proof.verification_scalars(n, &mut transcript) {
            Ok(v) => v, Err(_) => return false,
        };
        let u: Option<Vec<RistrettoPoint>> = proof.U_vecs.iter().flatten().map(|u| u.decompress()).collect();
        match u {
            Some(u) => s_p * p + msm(&s_u, &u) == msm(&s_g, g) + msm(&s_h, h) + s_q * q + msm(&s_pad, &pad_points),
            None => false,
        }
    }

    fn ecp_check(proof: &prove_ecp, n: usize, g: &[RistrettoPoint], c: &[RistrettoPoint], p_g: RistrettoPoint, p_c: RistrettoPoint) -> bool {
        let mut transcript = Transcript::new(b"ecp-test");
        let (z_s, s_p, s_a, z_pad, g_pad) = match proof.verification_scalars(n, &mut transcript) {
            Ok(v) => v, Err(_) => return false,
        };
        let a0: Option<Vec<RistrettoPoint>> = proof.A_vecs.iter().flatten().map(|a| a[0].decompress()).collect();
        let a1: Option<Vec<RistrettoPoint>> = proof.A_vecs.iter().flatten().map(|a| a[1].decompress()).collect();
        match (a0, a1) {
            (Some(a0), Some(a1)) => msm(&z_s, g) + msm(&z_pad, &g_pad) == s_p * p_g + msm(&s_a, &a0) && msm(&z_s[..c.len()], c) == s_p * p_c + msm(&s_a, &a1),
            _ => false,
        }
    }

    const CONFIGS: [(usize, usize); 5] = [(10, 4), (21, 3), (1001, 4), (1000, 5), (33, 2)];

    fn statement(n: usize, delta: Scalar) -> (Vec<RistrettoPoint>, Vec<RistrettoPoint>, RistrettoPoint, Vec<Scalar>, Vec<Scalar>, RistrettoPoint) {
        let (g, h, q) = (points(n), points(n), points(1)[0]);
        let (a, b) = (scalars(n), scalars(n));
        let p = msm(&a, &g) + msm(&b, &h) + (inner_product(&a, &b) + delta) * q;
        (g, h, q, a, b, p)
    }

    #[test]
    fn honest_padded_proofs_verify() {
        for &(n, k) in CONFIGS.iter() {
            let d = rounds(n, k);
            let (g, h, q, a, b, p) = statement(n, Scalar::ZERO);
            let proof = prove_ipa::create(&mut Transcript::new(b"ipa-test"), k, &g, &h, q, &a, &b, d);
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
                let (g, c, a) = (points(n), points(c_len), scalars(n));
                let (p_g, p_c) = (msm(&a, &g), msm(&a[..c_len], &c));
                let proof = prove_ecp::create(&mut Transcript::new(b"ecp-test"), k, &g, &c, &a, d);
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

        let g_pad = fold_pad_generators(IPA_PAD_G_DOMAIN, &seed, 3);
        assert_eq!(g_pad, fold_pad_generators(IPA_PAD_G_DOMAIN, &seed, 3));
        assert!(g_pad.iter().all(|p| *p != RistrettoPoint::default()));
        for domain in [IPA_PAD_H_DOMAIN, ECP_PAD_G_DOMAIN].iter() {
            let other = fold_pad_generators(domain, &seed, 3);
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
                    fold_pad_generators(IPA_PAD_G_DOMAIN, &seed, count);
                    fold_pad_generators(IPA_PAD_H_DOMAIN, &seed, count);
                    fold_pad_generators(ECP_PAD_G_DOMAIN, &seed, count);
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

    fn header(k: u64, d: u64, m: u64) -> Vec<u8> {
        let mut buf = vec![0u8; 96];
        buf[0..8].copy_from_slice(&k.to_le_bytes());
        buf[32..40].copy_from_slice(&d.to_le_bytes());
        buf[64..72].copy_from_slice(&m.to_le_bytes());
        buf
    }

    #[test]
    fn malformed_encodings_are_rejected() {
        let headers = [
            (0u64, 1u64, 1u64), (1, 1, 1), (65, 1, 1), (u64::max_value(), 1, 1),
            (4, 65, 1), (2, 1 << 40, 1), (4, 1, 0), (4, 1, u64::max_value()), (4, 1, 1 << 60),
        ];
        for &(k, d, m) in headers.iter() {
            let mut buf = header(k, d, m);
            buf.extend(vec![0u8; 32 * 8]);
            assert!(prove_ipa::from_bytes(&buf).is_err());
            assert!(prove_ecp::from_bytes(&buf).is_err());
        }

        let (g, h, q) = (points(10), points(10), points(1)[0]);
        let proof = prove_ipa::create(&mut Transcript::new(b"ipa-test"), 4, &g, &h, q, &scalars(10), &scalars(10), 2);
        let bytes = proof.to_bytes();
        
        assert!(prove_ipa::from_bytes(&bytes).is_ok());
        assert!(prove_ipa::from_bytes(&bytes[..bytes.len() - 32]).is_err());
        
        let mut longer = bytes.clone();
        longer.extend_from_slice(&[0u8; 32]);
        assert!(prove_ipa::from_bytes(&longer).is_err());

        let mut bad_k = proof.clone();
        bad_k.k = 0;
        assert!(bad_k.verification_scalars(10, &mut Transcript::new(b"ipa-test")).is_err());
    }
}