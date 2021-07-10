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
    bls12_377::{g1::Bls12_377G1Parameters, Fq, Fq2, Fr},
    traits::{ModelParameters, ShortWeierstrassParameters},
};

#[derive(Clone, Default, PartialEq, Eq)]
pub struct Bls12_377G2Parameters;

impl ModelParameters for Bls12_377G2Parameters {
    type BaseField = Fq2;
    type ScalarField = Fr;
}

impl ShortWeierstrassParameters for Bls12_377G2Parameters {
    /// AFFINE_GENERATOR_COEFFS = (G2_GENERATOR_X, G2_GENERATOR_Y)
    const AFFINE_GENERATOR_COEFFS: (Self::BaseField, Self::BaseField) = (G2_GENERATOR_X, G2_GENERATOR_Y);
    /// COEFF_A = [0, 0]
    const COEFF_A: Fq2 = field!(Fq2, Bls12_377G1Parameters::COEFF_A, Bls12_377G1Parameters::COEFF_A,);
    // As per https://eprint.iacr.org/2012/072.pdf,
    // this curve has b' = b/i, where b is the COEFF_B of G1, and x^6 -i is
    // the irreducible poly used to extend from Fp2 to Fp12.
    // In our case, i = u (App A.3, T_6).
    /// COEFF_B = [0,
    /// 155198655607781456406391640216936120121836107652948796323930557600032281009004493664981332883744016074664192874906]
    const COEFF_B: Fq2 = field!(
        Fq2,
        field!(Fq, BigInteger384([0, 0, 0, 0, 0, 0])),
        field!(
            Fq,
            BigInteger384([
                9255502405446297221,
                10229180150694123945,
                9215585410771530959,
                13357015519562362907,
                5437107869987383107,
                16259554076827459,
            ])
        ),
    );
    /// COFACTOR =
    /// 7923214915284317143930293550643874566881017850177945424769256759165301436616933228209277966774092486467289478618404761412630691835764674559376407658497
    const COFACTOR: &'static [u64] = &[
        0x0000000000000001,
        0x452217cc90000000,
        0xa0f3622fba094800,
        0xd693e8c36676bd09,
        0x8c505634fae2e189,
        0xfbb36b00e1dcc40c,
        0xddd88d99a6f6a829,
        0x26ba558ae9562a,
    ];
    /// COFACTOR_INV = COFACTOR^{-1} mod r
    /// = 6764900296503390671038341982857278410319949526107311149686707033187604810669
    const COFACTOR_INV: Fr = field!(
        Fr,
        BigInteger256([
            15499857013495546999,
            4613531467548868169,
            14546778081091178013,
            549402535258503313,
        ])
    );

    #[inline(always)]
    fn mul_by_a(_: &Self::BaseField) -> Self::BaseField {
        Self::BaseField::zero()
    }
}

pub const G2_GENERATOR_X: Fq2 = field!(Fq2, G2_GENERATOR_X_C0, G2_GENERATOR_X_C1);
pub const G2_GENERATOR_Y: Fq2 = field!(Fq2, G2_GENERATOR_Y_C0, G2_GENERATOR_Y_C1);

///
/// G2_GENERATOR_X_C0 =
/// 18530967594235566243335187101752570107616176349552784968178098996818868750252111351392075324115454717813888945791
///
/// See `snarkvm_algorithms::hash_to_curve::tests::bls12_377` for tests.
///
pub const G2_GENERATOR_X_C0: Fq = field!(
    Fq,
    BigInteger384::new([
        1970932785276074212,
        5313855799015095490,
        13710104135971762041,
        9664454070231379298,
        1816926557282441884,
        71411904752082374
    ])
);

///
/// G2_GENERATOR_X_C1 =
/// 249109238597864858227740027174673999737378771274637856066753519982906549035341230102237437984449583493201730309992
///
/// See `snarkvm_algorithms::hash_to_curve::tests::bls12_377` for tests.
///
pub const G2_GENERATOR_X_C1: Fq = field!(
    Fq,
    BigInteger384::new([
        5965396486954107648,
        16111224712623400997,
        2703376652134200593,
        18355826742575396191,
        9498717423363744549,
        4329860068425854
    ])
);

///
/// G2_GENERATOR_Y_C0 =
/// 162411681306238058413572478072422455473006141666469347219463629164083502715167424891268870041372045373590873694831
///
/// See `snarkvm_algorithms::hash_to_curve::tests::bls12_377` for tests.
///
pub const G2_GENERATOR_Y_C0: Fq = field!(
    Fq,
    BigInteger384::new([
        767052386591684706,
        4046053330946717442,
        107140035638630851,
        1214901647713936718,
        3003138019557670046,
        114940352679405637
    ])
);

///
/// G2_GENERATOR_Y_C1 =
/// 242659755380625277054368746168481273389655769841276332694767846852600636897945523549638958523260502082430026303549
///
/// See `snarkvm_algorithms::hash_to_curve::tests::bls12_377` for tests.
///
pub const G2_GENERATOR_Y_C1: Fq = field!(
    Fq,
    BigInteger384::new([
        9167062495373079174,
        3246999820078391825,
        17519529885154895381,
        1494814734789040059,
        17572559064583668264,
        118822025774994277
    ])
);
