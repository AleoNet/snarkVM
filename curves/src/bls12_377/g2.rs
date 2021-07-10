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
/// 114302662622654283009262358063160094701861582474466246461615450026008627444168110612821174822847374597554138837736
///
/// See `snarkvm_algorithms::hash_to_curve::tests::bls12_377` for tests.
///
pub const G2_GENERATOR_X_C0: Fq = field!(
    Fq,
    BigInteger384::new([
        856482368279856668,
        5793074389089131118,
        4596676208872117598,
        9025112746984268665,
        16328227140964044855,
        44781449420474798
    ])
);

///
/// G2_GENERATOR_X_C1 =
/// 177274492545224713145929754501896297323234812782955496673928274295405325233171369986159627920108686677981565796566
///
/// See `snarkvm_algorithms::hash_to_curve::tests::bls12_377` for tests.
///
pub const G2_GENERATOR_X_C1: Fq = field!(
    Fq,
    BigInteger384::new([
        12346803832623055560,
        4786264628284220908,
        6689501809078044958,
        675907838195598545,
        14712648858795088551,
        96143144554192752
    ])
);

///
/// G2_GENERATOR_Y_C0 =
/// 74332226801492097469250236843422197900845093148840025889564383194204142983525466020956549382567150819615871633674
///
/// See `snarkvm_algorithms::hash_to_curve::tests::bls12_377` for tests.
///
pub const G2_GENERATOR_Y_C0: Fq = field!(
    Fq,
    BigInteger384::new([
        7564421354282524249,
        11235739172967913084,
        721984723544260566,
        75889195665323699,
        11493645154932710602,
        12743107328700345
    ])
);

///
/// G2_GENERATOR_Y_C1 =
/// 120943082536536619052337621382347303140058776161798872583113748881793839821724088417521694169555147388195170408124
///
/// See `snarkvm_algorithms::hash_to_curve::tests::bls12_377` for tests.
///
pub const G2_GENERATOR_Y_C1: Fq = field!(
    Fq,
    BigInteger384::new([
        12086936954681951615,
        4444366098968706288,
        2347403901584830576,
        17264363775481626969,
        6042419194053018638,
        76454474019252244
    ])
);
