/// Variable-time MSM with Straus/Pippenger dispatch 
///
/// Dalek dispatches on size < 190 to Straus (NAF-5), else, use Pippenger.
/// We replicate that logic here for arkworks P-256, without touching the arkworks
/// library itself.  Both algorithms are variable-time; the mathematical result is
/// identical to `G::msm`.

use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BigInteger, PrimeField};


pub const STRAUS_THRESHOLD: usize = 190;


pub fn vartime_multiscalar_mul<G: CurveGroup>(
    scalars: &[G::ScalarField],
    bases: &[G::Affine],
) -> G {
    assert_eq!(scalars.len(), bases.len());
    let n = scalars.len();

    if n == 0 {
        return G::zero();
    }

    if n < STRAUS_THRESHOLD {
        straus_naf5::<G>(scalars, bases)
    } else {
        G::msm(bases, scalars).expect("MSM failed")
    }
}


// NAF-5 computation
#[inline(always)]
fn compute_naf_w5<F: PrimeField>(scalar: &F) -> [i8; 257] {
    let mut naf = [0i8; 257];

    let bytes = scalar.into_bigint().to_bytes_le();

    let mut x = [0u64; 5];
    for (i, chunk) in bytes.chunks(8).enumerate() {
        if i < 4 {
            let mut buf = [0u8; 8];
            buf[..chunk.len()].copy_from_slice(chunk);
            x[i] = u64::from_le_bytes(buf);
        }
    }

    const W: u64 = 5;
    const MASK: u64 = (1 << W) - 1;
    const HALF: u64 = 1 << (W - 1); 
    const FULL: u64 = 1 << W; 

    for i in 0..257usize {
        if x[0] == 0 && x[1] == 0 && x[2] == 0 && x[3] == 0 && x[4] == 0 {
            break;
        }

        if x[0] & 1 == 1 {
            let window = x[0] & MASK;

            if window >= HALF {
                let addend = FULL - window;
                let (v0, c) = x[0].overflowing_add(addend);
                x[0] = v0;
                let mut carry = c as u64;
                for limb in &mut x[1..] {
                    if carry == 0 {
                        break;
                    }
                    let (v, c2) = limb.overflowing_add(carry);
                    *limb = v;
                    carry = c2 as u64;
                }
                naf[i] = -(addend as i8);
            } else {
                let (v0, b) = x[0].overflowing_sub(window);
                x[0] = v0;
                let mut borrow = b as u64;
                for limb in &mut x[1..] {
                    if borrow == 0 {
                        break;
                    }
                    let (v, b2) = limb.overflowing_sub(borrow);
                    *limb = v;
                    borrow = b2 as u64;
                }
                naf[i] = window as i8;
            }
        }

        x[0] = (x[0] >> 1) | (x[1] << 63);
        x[1] = (x[1] >> 1) | (x[2] << 63);
        x[2] = (x[2] >> 1) | (x[3] << 63);
        x[3] = (x[3] >> 1) | (x[4] << 63);
        x[4] >>= 1;
    }

    naf
}


// Variable-time Straus MSM using NAF-5 scalar representation.
pub fn straus_naf5<G: CurveGroup>(scalars: &[G::ScalarField], bases: &[G::Affine]) -> G {
    let n = scalars.len();
    assert_eq!(n, bases.len());

    let nafs: Vec<[i8; 257]> = scalars.iter().map(|s| compute_naf_w5(s)).collect();
    let mut proj_flat: Vec<G> = Vec::with_capacity(n * 8);
    for base in bases {
        let p = (*base).into_group();
        let p2 = p.double(); 
        let mut cur = p;
        proj_flat.push(cur); 
        for _ in 1..8 {
            cur = cur + p2;
            proj_flat.push(cur); 
        }
    }

    let affine_flat: Vec<G::Affine> = G::normalize_batch(&proj_flat);

    let mut result = G::zero();

    for i in (0..257).rev() {
        result.double_in_place();

        for (j, naf) in nafs.iter().enumerate() {
            let digit = naf[i];
            if digit != 0 {
                let idx = (digit.unsigned_abs() as usize - 1) / 2;
                let entry = affine_flat[j * 8 + idx]; 
                if digit > 0 {
                    result += entry; 
                } else {
                    result -= entry; 
                }
            }
        }
    }

    result
}


#[cfg(test)]
mod tests {
    use super::*;
    use ark_ec::{AdditiveGroup, CurveGroup, VariableBaseMSM};
    use ark_secp256r1::{Fr as Scalar, Projective as G};
    use ark_std::{UniformRand, Zero};
    use std::time::Instant;

    /// Verify that straus_naf5 matches arkworks Pippenger for several widths < 190.
    #[test]
    fn test_straus_matches_pippenger() {
        println!("\n test_straus_matches_pippenger");

        let mut rng = ark_std::test_rng();

        for &n in &[1usize, 2, 4, 8, 16, 64, 189] {
            let scalars: Vec<_> = (0..n).map(|_| Scalar::rand(&mut rng)).collect();
            let bases: Vec<_> = (0..n).map(|_| G::rand(&mut rng).into_affine()).collect();

            let result_straus = straus_naf5::<G>(&scalars, &bases);
            let result_pippenger = G::msm(&bases, &scalars).unwrap();

            assert_eq!(
                result_straus, result_pippenger,
                "Straus vs Pippenger mismatch at n={}",
                n
            );
        }
    }

    /// Verify the dispatcher correctly routes small inputs to Straus and large to Pippenger.
    #[test]
    fn test_dispatch_routes_correctly() {
        println!("\n test_dispatch_routes_correctly");

        let mut rng = ark_std::test_rng();

        let n_small = 10usize;
        let scalars_s: Vec<_> = (0..n_small).map(|_| Scalar::rand(&mut rng)).collect();
        let bases_s: Vec<_> = (0..n_small)
            .map(|_| G::rand(&mut rng).into_affine())
            .collect();
        let r_straus = vartime_multiscalar_mul::<G>(&scalars_s, &bases_s);
        let r_pip = G::msm(&bases_s, &scalars_s).unwrap();
        assert_eq!(r_straus, r_pip, "dispatch small mismatch");

        let n_large = 200usize;
        let scalars_l: Vec<_> = (0..n_large).map(|_| Scalar::rand(&mut rng)).collect();
        let bases_l: Vec<_> = (0..n_large)
            .map(|_| G::rand(&mut rng).into_affine())
            .collect();
        let r_disp = vartime_multiscalar_mul::<G>(&scalars_l, &bases_l);
        let r_pip2 = G::msm(&bases_l, &scalars_l).unwrap();
        assert_eq!(r_disp, r_pip2, "dispatch large mismatch");
    }

    fn time_fn_ns(iters: u32, mut f: impl FnMut()) -> u64 {
        f(); 
        let t = Instant::now();
        for _ in 0..iters {
            f();
        }
        t.elapsed().as_nanos() as u64 / iters as u64
    }

    #[test]
    fn test_straus_latency_vs_pippenger() {
        let mut rng = ark_std::test_rng();

        println!("\n test_straus_latency_vs_pippenger");
        println!(
            "  {:>5}  {:>12}  {:>12}  {:>10}",
            "n", "Straus (us)", "Pippenger (us)", "Speedup"
        );
        println!("  {}", "-".repeat(46));

        for &n in &[1usize, 2, 3, 4, 7, 8, 16, 32, 64, 128, 189, 65536] {
            let scalars: Vec<_> = (0..n).map(|_| Scalar::rand(&mut rng)).collect();
            let bases: Vec<_> = (0..n).map(|_| G::rand(&mut rng).into_affine()).collect();

            let iters = (4_000_000u64 / (n as u64 * 500).max(2000)).max(10) as u32;

            let straus_ns = time_fn_ns(iters, || {
                let _ = straus_naf5::<G>(&scalars, &bases);
            });
            let pip_ns = time_fn_ns(iters, || {
                let _ = G::msm(&bases, &scalars).unwrap();
            });
            let speedup = pip_ns as f64 / straus_ns as f64;

            println!(
                "  {:>5}  {:>12.1}  {:>12.1}  {:>9.2} times",
                n,
                straus_ns as f64 / 1_000.0,
                pip_ns as f64 / 1_000.0,
                speedup,
            );

            // Correctness check
            let rs = straus_naf5::<G>(&scalars, &bases);
            let rp = G::msm(&bases, &scalars).unwrap();
            assert_eq!(rs, rp, "mismatch at n={}", n);
        }
        println!();
    }

    #[test]
    fn test_straus_phase_timing_n4() {
        println!("\n test_straus_phase_timing_n4");

        let mut rng = ark_std::test_rng();
        let n = 4usize;
        let scalars: Vec<Scalar> = (0..n).map(|_| Scalar::rand(&mut rng)).collect();
        let bases: Vec<<G as CurveGroup>::Affine> =
            (0..n).map(|_| G::rand(&mut rng).into_affine()).collect();

        let iters = 5_000u32;

        let naf_ns = time_fn_ns(iters, || {
            let _: Vec<[i8; 257]> = scalars.iter().map(|s| compute_naf_w5(s)).collect();
        });

        let table_ns = time_fn_ns(iters, || {
            let mut proj: Vec<G> = Vec::with_capacity(n * 8);
            for base in &bases {
                let p = (*base).into_group();
                let p2 = p.double();
                let mut cur = p;
                proj.push(cur);
                for _ in 1..8 {
                    cur = cur + p2;
                    proj.push(cur);
                }
            }
            let _ = G::normalize_batch(&proj);
        });

        let nafs: Vec<[i8; 257]> = scalars.iter().map(|s| compute_naf_w5(s)).collect();
        let mut proj: Vec<G> = Vec::with_capacity(n * 8);
        for base in &bases {
            let p = (*base).into_group();
            let p2 = p.double();
            let mut cur = p;
            proj.push(cur);
            for _ in 1..8 {
                cur = cur + p2;
                proj.push(cur);
            }
        }
        let aff: Vec<<G as CurveGroup>::Affine> = G::normalize_batch(&proj);

        let loop_ns = time_fn_ns(iters, || {
            let mut result = G::zero();
            for i in (0..257).rev() {
                result.double_in_place();
                for j in 0..n {
                    let digit = nafs[j][i];
                    if digit != 0 {
                        let idx = (digit.unsigned_abs() as usize - 1) / 2;
                        let entry = aff[j * 8 + idx];
                        if digit > 0 {
                            result += entry;
                        } else {
                            result -= entry;
                        }
                    }
                }
            }
            let _ = result;
        });

        let total_ns = naf_ns + table_ns + loop_ns;

        println!();
        println!(
            "  straus_naf5 v2 phase breakdown (n={}, {} iters):",
            n, iters
        );
        println!(
            "    NAF computation:  {:>8.1} us  ({:4.1}%)",
            naf_ns as f64 / 1e3,
            naf_ns as f64 / total_ns as f64 * 100.0
        );
        println!(
            "    Table build+norm: {:>8.1} us  ({:4.1}%)",
            table_ns as f64 / 1e3,
            table_ns as f64 / total_ns as f64 * 100.0
        );
        println!(
            "    Main eval loop:   {:>8.1} us  ({:4.1}%)",
            loop_ns as f64 / 1e3,
            loop_ns as f64 / total_ns as f64 * 100.0
        );
        println!("    Total (phases):   {:>8.1} us", total_ns as f64 / 1e3);
        println!();

        let pip_ns = time_fn_ns(5_000, || {
            let _ = G::msm(&bases, &scalars).unwrap();
        });
        println!("    Pippenger (n=4):  {:>8.1} us", pip_ns as f64 / 1e3);
        println!(
            "    Straus speedup:   {:>8.2} times",
            pip_ns as f64 / total_ns as f64
        );
        println!();
    }
    
}
