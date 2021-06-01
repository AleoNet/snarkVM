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

use snarkvm_curves::{bls12_377::G1Affine, traits::AffineCurve};
use snarkvm_fields::{Field, Zero};

#[cfg(feature = "blstasm")]
mod asm;
mod standard;

#[cfg(all(feature = "blstasm", not(target_arch = "x86_64")))]
compile_error!("`blstasm` feature is only supported on x86_64");

pub struct VariableBaseMSM;

impl VariableBaseMSM {
    #[allow(unused)]
    fn msm_basic<G: AffineCurve>(bases: &[G], scalars: &[<G::ScalarField as Field>::BigInteger]) -> G::Projective {
        let mut acc = G::Projective::zero();

        for (base, scalar) in bases.iter().zip(scalars.iter()) {
            acc += &base.mul(*scalar);
        }
        acc
    }

    pub fn multi_scalar_mul_safe<G: AffineCurve>(
        bases: &[G],
        scalars: &[<G::ScalarField as Field>::BigInteger],
    ) -> G::Projective {
        standard::msm_standard(bases, scalars)
    }

    pub fn multi_scalar_mul<G: AffineCurve>(
        bases: &[G],
        scalars: &[<G::ScalarField as Field>::BigInteger],
    ) -> G::Projective {
        if TypeId::of::<G>() == TypeId::of::<G1Affine>() {
            #[cfg(feature = "blstasm")]
            {
                return asm::msm_asm(bases, scalars);
            }
        }
        standard::msm_standard(bases, scalars)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;
    use snarkvm_curves::{
        bls12_377::{Fr, G1Affine, G1Projective},
        traits::ProjectiveCurve,
    };
    use snarkvm_fields::PrimeField;
    use snarkvm_utilities::{rand::UniformRand, BigInteger256};

    fn test_data(samples: usize) -> (Vec<G1Affine>, Vec<BigInteger256>) {
        let mut rng = XorShiftRng::seed_from_u64(234872846u64);

        let v = (0..samples).map(|_| Fr::rand(&mut rng).into_repr()).collect::<Vec<_>>();
        let g = (0..samples)
            .map(|_| G1Projective::rand(&mut rng).into_affine())
            .collect::<Vec<_>>();

        (g, v)
    }

    #[test]
    fn test_basic() {
        let (bases, scalars) = test_data(100);
        let rust = standard::msm_standard(bases.as_slice(), scalars.as_slice());
        let basic = VariableBaseMSM::msm_basic(bases.as_slice(), scalars.as_slice());
        assert_eq!(rust, basic);
    }

    #[test]
    fn test_msm_asm() {
        let (bases, scalars) = test_data(1 << 10);
        let rust = standard::msm_standard(bases.as_slice(), scalars.as_slice());
        let asm = asm::msm_asm(bases.as_slice(), scalars.as_slice());
        assert_eq!(rust, asm);
    }

}
