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

use snarkvm_fields::{field, Zero};
use snarkvm_utilities::biginteger::{BigInteger256, BigInteger384};

use crate::{
    bls12_377::{Fq, Fr},
    traits::{ModelParameters, ShortWeierstrassParameters},
};

#[derive(Clone, Default, PartialEq, Eq)]
pub struct Bls12_377G1Parameters;

impl ModelParameters for Bls12_377G1Parameters {
    type BaseField = Fq;
    type ScalarField = Fr;
}

impl ShortWeierstrassParameters for Bls12_377G1Parameters {
    /// AFFINE_GENERATOR_COEFFS = (G1_GENERATOR_X, G1_GENERATOR_Y)
    const AFFINE_GENERATOR_COEFFS: (Self::BaseField, Self::BaseField) = (G1_GENERATOR_X, G1_GENERATOR_Y);
    /// COEFF_A = 0
    const COEFF_A: Fq = field!(Fq, BigInteger384([0x0, 0x0, 0x0, 0x0, 0x0, 0x0]));
    /// COEFF_B = 1
    const COEFF_B: Fq = field!(
        Fq,
        BigInteger384([
            0x2cdffffffffff68,
            0x51409f837fffffb1,
            0x9f7db3a98a7d3ff2,
            0x7b4e97b76e7c6305,
            0x4cf495bf803c84e8,
            0x8d6661e2fdf49a,
        ])
    );
    /// COFACTOR = (x - 1)^2 / 3  = 30631250834960419227450344600217059328
    const COFACTOR: &'static [u64] = &[0x0, 0x170b5d4430000000];
    /// COFACTOR_INV = COFACTOR^{-1} mod r
    /// = 5285428838741532253824584287042945485047145357130994810877
    const COFACTOR_INV: Fr = field!(
        Fr,
        BigInteger256([
            2013239619100046060,
            4201184776506987597,
            2526766393982337036,
            1114629510922847535,
        ])
    );

    #[inline(always)]
    fn mul_by_a(_: &Self::BaseField) -> Self::BaseField {
        Self::BaseField::zero()
    }
}

///
/// G1_GENERATOR_X =
/// 180626689152567938232604559698399306213229526488826235533375072902470977089128486884883292831560455202598472059967
///
/// See `snarkvm_algorithms::hash_to_curve::tests::bls12_377` for tests.
///
pub const G1_GENERATOR_X: Fq = field!(
    Fq,
    BigInteger384::new([
        9865942535067768194,
        2790942630984681348,
        7918410467197438669,
        13719405186099626186,
        15702043047188965378,
        114833063042186202
    ])
);

///
/// G1_GENERATOR_Y =
/// 104978230256306450211782082207474713267703681175513107150081277237522362137760830051589443929748884756921100615233
///
/// See `snarkvm_algorithms::hash_to_curve::tests::bls12_377` for tests.
///
pub const G1_GENERATOR_Y: Fq = field!(
    Fq,
    BigInteger384::new([
        3932736639468406888,
        13616733865822217238,
        2004500162067749076,
        17350864265395732105,
        17971100192741911999,
        16412267610233764
    ])
);
