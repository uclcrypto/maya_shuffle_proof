#![allow(non_snake_case)]

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::VartimeMultiscalarMul;
use merlin::Transcript;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

use errors::ProofError;
use std::convert::TryInto;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Instant;
use transcript::TranscriptProtocol;

static IPP_TIMING_PRINTED: AtomicBool = AtomicBool::new(false);
static ECP_TIMING_PRINTED: AtomicBool = AtomicBool::new(false);

struct KnownSizeIter<I: Iterator> {
    inner: I,
    remaining: usize,
}
impl<I: Iterator> KnownSizeIter<I> {
    fn new(inner: I, size: usize) -> Self {
        Self {
            inner,
            remaining: size,
        }
    }
}
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

            #[cfg(not(feature = "global_padding"))]
            {
                let rem = n_j % k;
                if rem != 0 {
                    let pad = k - rem;
                    a_curr.extend(std::iter::repeat(Scalar::ZERO).take(pad));
                    b_curr.extend(std::iter::repeat(Scalar::ZERO).take(pad));
                    g_curr.extend(std::iter::repeat(RistrettoPoint::default()).take(pad));
                    h_curr.extend(std::iter::repeat(RistrettoPoint::default()).take(pad));
                    n_j += pad;
                }
            }
            #[cfg(feature = "global_padding")]
            {
                debug_assert_eq!(n_j % k, 0,
                    "global_padding: n_j={} must be divisible by k={} (caller must pre-pad to m*k^d)", n_j, k);
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
    ) -> Result<(Vec<Scalar>, Vec<Scalar>, Scalar, Scalar, Vec<Scalar>), ProofError> {
        let k = self.k;
        if n == 0 {
            return Err(ProofError::InvalidGeneratorsLength);
        }
        let d = self.U_vecs.len();

        let round_lengths = reconstruct_round_lengths(n, k, d);
        let m = *round_lengths.last().unwrap();

        if self.a_final.len() != m || self.b_final.len() != m {
            return Err(ProofError::VerificationError);
        }

        transcript.append_message(b"protocol-name", b"k_bullet_delay");
        transcript.append_message(b"n", &(n as u64).to_le_bytes());
        transcript.append_message(b"k", &(k as u64).to_le_bytes());

        let mut challenges: Vec<Scalar> = Vec::with_capacity(d);

        for r in 0..d {
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

        let mut s_P = Scalar::ONE;
        let k_minus_1_exp = (k - 1) as u64;
        let mut c_k_minus_1_products = vec![Scalar::ONE; d];
        let mut product_so_far = Scalar::ONE;
        for r in (0..d).rev() {
            let c_k_minus_1 = scalar_pow(challenges[r], k_minus_1_exp);
            c_k_minus_1_products[r] = product_so_far;
            product_so_far *= c_k_minus_1;
        }
        s_P = product_so_far;

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

            next_s.truncate(round_lengths[r]);
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

            next_s.truncate(round_lengths[r]);
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

        Ok((s_g_full, s_h_full, s_Q_final, s_P, s_U))
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
            #[cfg(not(feature = "global_padding"))]
            {
                let rem = n_j % k;
                if rem != 0 {
                    let pad = k - rem;
                    a_curr.extend(std::iter::repeat(Scalar::ZERO).take(pad));
                    G_curr.extend(std::iter::repeat(RistrettoPoint::default()).take(pad));
                    C1_curr.extend(std::iter::repeat(RistrettoPoint::default()).take(pad));
                    n_j += pad;
                }
            }
            #[cfg(feature = "global_padding")]
            {
                debug_assert_eq!(n_j % k, 0,
                    "global_padding: n_j={} must be divisible by k={} (caller must pre-pad to m*k^d)", n_j, k);
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
    ) -> Result<(Vec<Scalar>, Scalar, Vec<Scalar>), ProofError> {
        let k = self.k;
        let d = self.A_vecs.len();

        let round_lengths = reconstruct_round_lengths(n, k, d);
        let m = *round_lengths.last().unwrap();

        if self.z.len() != m {
            return Err(ProofError::VerificationError);
        }

        transcript.append_message(b"protocol-name", b"k_ipp_delay_2");
        transcript.append_message(b"n", &(n as u64).to_le_bytes());
        transcript.append_message(b"k", &(k as u64).to_le_bytes());

        let mut challenges: Vec<Scalar> = Vec::with_capacity(d);
        for r in 0..d {
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

        let mut s_P = Scalar::ONE;
        let k_exp = k as u64;
        let mut c_k_products = vec![Scalar::ONE; d];
        let mut product_so_far = Scalar::ONE;
        for r in (0..d).rev() {
            let c_k = scalar_pow(challenges[r], k_exp);
            c_k_products[r] = product_so_far;
            product_so_far *= c_k;
        }
        s_P = product_so_far;

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

            next_s.truncate(round_lengths[r]);
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

        Ok((z_s_vec, s_P, s_A_vec))
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
