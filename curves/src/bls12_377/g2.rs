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
/// 46569348160334319069206848238213973843469189214461431993285766877825396394318396555703037114246793801437027641255
///
/// See `snarkvm_algorithms::hash_to_curve::tests::bls12_377` for tests.
///
pub const G2_GENERATOR_X_C0: Fq = field!(
    Fq,
    BigInteger384::new([
        11973342190133476562,
        7932516760210873444,
        3123660938736867083,
        3711726067984912930,
        10170985402718536061,
        102187153343817403
    ])
);

///
/// G2_GENERATOR_X_C1 =
/// 188412368947954446259048493756673862317357819827884613309550352254310070810851839417320244506424991334079916039560
///
/// See `snarkvm_algorithms::hash_to_curve::tests::bls12_377` for tests.
///
pub const G2_GENERATOR_X_C1: Fq = field!(
    Fq,
    BigInteger384::new([
        16848003768709251513,
        8558673495899769328,
        5083675993247777120,
        3470484689664808427,
        4319033446732408080,
        22004849378974139
    ])
);

///
/// G2_GENERATOR_Y_C0 =
/// 158561138871920333147708562303794116026060566044009338691828247707987279531554093137508523592988442410034102129831
///
/// See `snarkvm_algorithms::hash_to_curve::tests::bls12_377` for tests.
///
pub const G2_GENERATOR_Y_C0: Fq = field!(
    Fq,
    BigInteger384::new([
        17087946985508632415,
        6250381662614363525,
        1686999626994196013,
        13584694043776821853,
        8523762154632676039,
        108956758486672228
    ])
);

///
/// G2_GENERATOR_Y_C1 =
/// 32057641082752786628002279460430111176039873268008259885923512719033298568522407836278114602800860283800447442580
///
/// See `snarkvm_algorithms::hash_to_curve::tests::bls12_377` for tests.
///
pub const G2_GENERATOR_Y_C1: Fq = field!(
    Fq,
    BigInteger384::new([
        5428705130058419830,
        13435523325207739993,
        9912851198364072856,
        10812231845306851609,
        11214316695400868122,
        90921991426512422
    ])
);
