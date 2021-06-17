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
use snarkvm_fields::{PrimeField, Zero};

mod standard;

pub struct VariableBaseMSM;

impl VariableBaseMSM {
    pub fn multi_scalar_mul<G: AffineCurve>(
        bases: &[G],
        scalars: &[<G::ScalarField as PrimeField>::BigInteger],
    ) -> G::Projective {
        standard::msm_standard(bases, scalars)
    }

    #[allow(unused)]
    fn msm_naive<G: AffineCurve>(bases: &[G], scalars: &[<G::ScalarField as PrimeField>::BigInteger]) -> G::Projective {
        let mut acc = G::Projective::zero();

        for (base, scalar) in bases.iter().zip(scalars.iter()) {
            acc += &base.mul(*scalar);
        }
        acc
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
    fn test_naive() {
        let (bases, scalars) = test_data(100);
        let rust = standard::msm_standard(bases.as_slice(), scalars.as_slice());
        let naive = VariableBaseMSM::msm_naive(bases.as_slice(), scalars.as_slice());
        assert_eq!(rust, naive);
    }
}
