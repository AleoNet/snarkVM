// Copyright (C) 2019-2021 Aleo Systems Inc.
// This file is part of the snarkVM library.

// The snarkVM library is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// The snarkVM library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with the snarkVM library. If not, see <https://www.gnu.org/licenses/>.

use snarkvm_curves::traits::AffineCurve;
use snarkvm_fields::{Field, PrimeField, FieldParameters, Zero};
use snarkvm_utilities::biginteger::BigInteger;

pub enum MsmMode {
    Rust,
    RustBasic,
    Assembly,
    Cuda,
}

#[cfg(feature = "parallel")]
use rayon::prelude::*;

#[cfg(feature = "blstasm")]
#[link(name = "blst377", kind = "static")]
extern "C" {
    pub fn msm_pippenger_6(
        result: *mut u64,
        bases_in: *const u8,
        scalars_in: *const u8,
        num_pairs: usize,
        scalar_bits: usize,
        c: usize,
    );
}

pub struct VariableBaseMSM;

impl VariableBaseMSM {
    #[cfg(feature = "cuda")]
    fn msm_inner_cuda<G: AffineCurve>(bases: &[G], scalars: &[<G::ScalarField as Field>::BigInteger]) -> Result<G::Projective, cuda_oxide::ErrorCode> {
        super::cuda::msm_cuda(bases, scalars)
    }

    fn msm_inner_basic<G: AffineCurve>(bases: &[G], scalars: &[<G::ScalarField as Field>::BigInteger]) -> G::Projective {
        let mut acc = G::Projective::zero();

        for (base, scalar) in bases.iter().zip(scalars.iter()) {
            acc += &base.mul(*scalar);
        }
        acc
    }

    #[cfg(feature = "blstasm")]
    fn msm_inner_asm<G: AffineCurve>(bases: &[G], scalars: &[<G::ScalarField as Field>::BigInteger]) -> G::Projective {
        if scalars.len() < 4 {
            let mut acc = G::Projective::zero();

            for (base, scalar) in bases.iter().zip(scalars.iter()) {
                acc += &base.mul(*scalar);
            }
            return acc;
        }

        let c = if scalars.len() < 32 {
            3
        } else {
            (2.0 / 3.0 * (f64::from(scalars.len() as u32)).log2() + 2.0).ceil() as usize
        };
        let num_bits = <G::ScalarField as PrimeField>::Parameters::MODULUS_BITS as usize;

        let mut sn_result = G::Projective::zero();

        unsafe {
            let bases_raw = &*(bases.as_ptr() as *const u8);
            let scalars_raw = &*(scalars.as_ptr() as *const u8);
            #[allow(trivial_casts)]
            let sn_result_raw = std::slice::from_raw_parts_mut(&mut sn_result as *mut _ as *mut u64, 18);
            msm_pippenger_6(
                sn_result_raw.as_mut_ptr(),
                bases_raw,
                scalars_raw,
                scalars.len(),
                num_bits,
                c,
            );
        }
        sn_result
    }

    fn msm_inner_rust<G: AffineCurve>(bases: &[G], scalars: &[<G::ScalarField as Field>::BigInteger]) -> G::Projective {
        use snarkvm_fields::One;
        use snarkvm_curves::traits::ProjectiveCurve;

        let c = 1;/*if scalars.len() < 32 {
            3
        } else {
            (2.0 / 3.0 * (f64::from(scalars.len() as u32)).log2() + 2.0).ceil() as usize
        };*/

        let num_bits = <G::ScalarField as PrimeField>::Parameters::MODULUS_BITS as usize;
        let fr_one = G::ScalarField::one().into_repr();

        let zero = G::zero().into_projective();
        let window_starts: Vec<_> = (0..num_bits).step_by(c).collect();

        // Each window is of size `c`.
        // We divide up the bits 0..num_bits into windows of size `c`, and
        // in parallel process each such window.
        let window_sums: Vec<_> = window_starts.into_iter() // cfg_into_iter!(window_starts)
            .map(|w_start| {
                let mut res = zero;
                // We don't need the "zero" bucket, so we only have 2^c - 1 buckets
                let mut buckets = vec![zero; (1 << c) - 1];
                scalars
                    .iter()
                    .zip(bases)
                    .filter(|(s, _)| !s.is_zero())
                    .for_each(|(&scalar, base)| {
                        if scalar == fr_one {
                            // We only process unit scalars once in the first window.
                            if w_start == 0 {
                                res.add_assign_mixed(base);
                            }
                        } else {
                            let mut scalar = scalar;

                            // We right-shift by w_start, thus getting rid of the
                            // lower bits.
                            scalar.divn(w_start as u32);

                            // We mod the remaining bits by the window size.
                            let scalar = scalar.as_ref()[0] % (1 << c);

                            // If the scalar is non-zero, we update the corresponding
                            // bucket.
                            // (Recall that `buckets` doesn't have a zero bucket.)
                            if scalar != 0 {
                                buckets[(scalar - 1) as usize].add_assign_mixed(&base);
                            }
                        }
                    });
                G::Projective::batch_normalization(&mut buckets);

                let mut running_sum = G::Projective::zero();
                for (i, proj) in buckets.into_iter().enumerate().rev() {
                    // println!("r-t{}:pre: bucket {}: bx={} by={} bz={}", w, i, proj.to_x_coordinate().as_repr_singlet().unwrap().clone().as_ref()[0], proj.to_y_coordinate().as_repr_singlet().unwrap().clone().as_ref()[0], proj.to_z_coordinate().as_repr_singlet().unwrap().clone().as_ref()[0]);
                    let affine = proj.into_affine();
                    // println!("r-t{}:affine: bucket {}: ax={} ay={}", w, i, affine.to_x_coordinate().as_repr_singlet().unwrap().clone().as_ref()[0], affine.to_y_coordinate().as_repr_singlet().unwrap().clone().as_ref()[0]);
                    running_sum.add_assign_mixed(&affine);
                    // println!("r-t{}:added: bucket {}: sx={} sy={} sz={}", w, i, running_sum.to_x_coordinate().as_repr_singlet().unwrap().clone().as_ref()[0], running_sum.to_y_coordinate().as_repr_singlet().unwrap().clone().as_ref()[0], running_sum.to_z_coordinate().as_repr_singlet().unwrap().clone().as_ref()[0]);
                    res += &running_sum;
                    // println!("r-t{}:committed: bucket {}: ox={} oy={} oz={}", w_start, i, res.to_x_coordinate().as_repr_singlet().unwrap().clone().as_ref()[0], res.to_y_coordinate().as_repr_singlet().unwrap().clone().as_ref()[0], res.to_z_coordinate().as_repr_singlet().unwrap().clone().as_ref()[0]);
                }
                // for b in buckets.into_iter().map(|g| g.into_affine()).rev() {
                //     running_sum.add_assign_mixed(&b);
                //     res += &running_sum;
                // }

                res
            })
            .collect();

        // We store the sum for the lowest window.
        let lowest = window_sums.first().unwrap();

        // We're traversing windows from high to low.
        window_sums[1..].iter().rev().fold(zero, |mut total, sum_i| {
            total += sum_i;
            for _ in 0..c {
                total.double_in_place();
            }
            total
        }) + lowest
    }

    pub fn multi_scalar_mul<G: AffineCurve>(
        bases: &[G],
        scalars: &[<G::ScalarField as Field>::BigInteger],
    ) -> G::Projective {
        // Self::msm_inner_rust(bases, scalars)
        // Self::msm_inner_asm(bases, scalars)
        Self::msm_inner_cuda(bases, scalars).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;
    use snarkvm_curves::{bls12_377::{Fr, G1Affine, G1Projective}, traits::ProjectiveCurve};
    use snarkvm_fields::PrimeField;
    use snarkvm_utilities::{BigInteger256, rand::UniformRand};


    fn test_data(samples: usize) -> (Vec<G1Affine>, Vec<BigInteger256>) {
        let mut rng = XorShiftRng::seed_from_u64(234872846u64);

        let v = (0..samples).map(|_| Fr::rand(&mut rng).into_repr()).collect::<Vec<_>>();
        let g = (0..samples)
            .map(|_| G1Projective::rand(&mut rng).into_affine())
            .collect::<Vec<_>>();
    
        (g, v)
    }

    #[test]
    fn test_msm_basic() {
        let (bases, scalars) = test_data(3);
        let rust = VariableBaseMSM::msm_inner_rust(bases.as_slice(), scalars.as_slice());
        let basic = VariableBaseMSM::msm_inner_basic(bases.as_slice(), scalars.as_slice());
        assert_eq!(rust, basic);
    }

    #[test]
    fn test_msm_asm() {
        let (bases, scalars) = test_data(1 << 10);
        let rust = VariableBaseMSM::msm_inner_rust(bases.as_slice(), scalars.as_slice());
        let asm = VariableBaseMSM::msm_inner_asm(bases.as_slice(), scalars.as_slice());
        assert_eq!(rust, asm);
    }

    #[test]
    fn test_msm_cuda() {
        let (bases, scalars) = test_data(1 << 10);
        let rust = VariableBaseMSM::msm_inner_rust(bases.as_slice(), scalars.as_slice());

        let cuda = VariableBaseMSM::msm_inner_cuda(bases.as_slice(), scalars.as_slice()).unwrap();
        assert_eq!(rust, cuda);
    }
}