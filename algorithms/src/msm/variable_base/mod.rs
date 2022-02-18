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

use std::any::TypeId;

#[cfg(all(feature = "cuda", target_arch = "x86_64"))]
use std::sync::atomic::{AtomicBool, Ordering};

use snarkvm_curves::{bls12_377::G1Affine, traits::AffineCurve};
use snarkvm_fields::PrimeField;

mod standard;

#[cfg(all(feature = "cuda", target_arch = "x86_64"))]
mod cuda;

#[cfg(all(feature = "cuda", target_arch = "x86_64"))]
static HAS_CUDA_FAILED: AtomicBool = AtomicBool::new(false);

#[derive(Copy, Clone, Debug)]
pub enum MSMStrategy {
    Standard,
    BatchedA,
    BatchedB,
}

pub struct VariableBaseMSM;

impl VariableBaseMSM {
    pub fn multi_scalar_mul<G: AffineCurve>(
        bases: &[G],
        scalars: &[<G::ScalarField as PrimeField>::BigInteger],
    ) -> G::Projective {
        if TypeId::of::<G>() == TypeId::of::<G1Affine>() {
            #[cfg(all(feature = "cuda", target_arch = "x86_64"))]
            {
                if !HAS_CUDA_FAILED.load(Ordering::SeqCst) {
                    match cuda::msm_cuda(bases, scalars) {
                        Ok(x) => return x,
                        Err(_e) => {
                            HAS_CUDA_FAILED.store(true, Ordering::SeqCst);
                            eprintln!("CUDA failed, moving to next msm method.");
                        }
                    }
                }
            }
        }
        standard::msm(bases, scalars, MSMStrategy::BatchedA)
    }

    pub fn msm<G: AffineCurve>(
        bases: &[G],
        scalars: &[<G::ScalarField as PrimeField>::BigInteger],
        strategy: MSMStrategy,
    ) -> G::Projective {
        if TypeId::of::<G>() == TypeId::of::<G1Affine>() {
            #[cfg(all(feature = "cuda", target_arch = "x86_64"))]
            {
                if !HAS_CUDA_FAILED.load(Ordering::SeqCst) {
                    match cuda::msm_cuda(bases, scalars) {
                        Ok(x) => return x,
                        Err(_e) => {
                            HAS_CUDA_FAILED.store(true, Ordering::SeqCst);
                            eprintln!("CUDA failed, moving to next msm method.");
                        }
                    }
                }
            }
        }
        standard::msm(bases, scalars, strategy)
    }

    #[cfg(test)]
    fn msm_naive<G: AffineCurve>(bases: &[G], scalars: &[<G::ScalarField as PrimeField>::BigInteger]) -> G::Projective {
        use snarkvm_fields::Zero;
        use snarkvm_utilities::BitIteratorBE;

        let mut acc = G::Projective::zero();
        for (base, scalar) in bases.iter().zip(scalars.iter()) {
            acc += base.mul_bits(BitIteratorBE::new(*scalar));
        }
        acc
    }

    #[cfg(test)]
    fn msm_naive_parallel<G: AffineCurve>(
        bases: &[G],
        scalars: &[<G::ScalarField as PrimeField>::BigInteger],
    ) -> G::Projective {
        use rayon::prelude::*;
        use snarkvm_utilities::BitIteratorBE;

        bases
            .par_iter()
            .zip_eq(scalars.par_iter())
            .map(|(base, scalar)| base.mul_bits(BitIteratorBE::new(*scalar)))
            .sum()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_curves::bls12_377::{Fr, G1Affine};
    use snarkvm_fields::PrimeField;
    use snarkvm_utilities::rand::test_rng;

    use rand_xorshift::XorShiftRng;

    fn create_scalar_bases<G: AffineCurve<ScalarField = F>, F: PrimeField>(
        rng: &mut XorShiftRng,
        size: usize,
    ) -> (Vec<G>, Vec<F::BigInteger>) {
        let bases = (0..size).map(|_| G::rand(rng)).collect::<Vec<_>>();
        let scalars = (0..size).map(|_| F::rand(rng).to_repr()).collect::<Vec<_>>();
        (bases, scalars)
    }

    #[test]
    fn test_msm() {
        let mut rng = test_rng();
        let (bases, scalars) = create_scalar_bases::<G1Affine, Fr>(&mut rng, 1000);

        let naive_a = VariableBaseMSM::msm_naive(bases.as_slice(), scalars.as_slice());
        let naive_b = VariableBaseMSM::msm_naive_parallel(bases.as_slice(), scalars.as_slice());
        assert_eq!(naive_a, naive_b);

        let candidate = standard::msm(bases.as_slice(), scalars.as_slice(), MSMStrategy::Standard);
        assert_eq!(naive_a, candidate);

        let candidate = standard::msm(bases.as_slice(), scalars.as_slice(), MSMStrategy::BatchedA);
        assert_eq!(naive_a, candidate);

        let candidate = standard::msm(bases.as_slice(), scalars.as_slice(), MSMStrategy::BatchedB);
        assert_eq!(naive_a, candidate);
    }

    #[cfg(all(feature = "cuda", target_arch = "x86_64"))]
    #[test]
    fn test_msm_cuda() {
        let mut rng = test_rng();
        for _ in 0..100 {
            let (bases, scalars) = create_scalar_bases::<G1Affine, Fr>(&mut rng, 1 << 10);
            let rust = standard::msm(bases.as_slice(), scalars.as_slice(), MSMStrategy::BatchedA);

            let cuda = cuda::msm_cuda(bases.as_slice(), scalars.as_slice()).unwrap();
            assert_eq!(rust, cuda);
        }
    }
}
