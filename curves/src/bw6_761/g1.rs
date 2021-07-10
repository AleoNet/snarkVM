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
use snarkvm_utilities::biginteger::{BigInteger384, BigInteger768};

use crate::{
    bw6_761::{Fq, Fr},
    traits::{ModelParameters, ShortWeierstrassParameters},
};

#[derive(Clone, Default, PartialEq, Eq)]
pub struct BW6_761G1Parameters;

impl ModelParameters for BW6_761G1Parameters {
    type BaseField = Fq;
    type ScalarField = Fr;
}

impl ShortWeierstrassParameters for BW6_761G1Parameters {
    /// AFFINE_GENERATOR_COEFFS = (G1_GENERATOR_X, G1_GENERATOR_Y)
    const AFFINE_GENERATOR_COEFFS: (Self::BaseField, Self::BaseField) = (G1_GENERATOR_X, G1_GENERATOR_Y);
    /// COEFF_A = 0
    const COEFF_A: Fq = field!(Fq, BigInteger768([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]));
    /// COEFF_B = -1
    const COEFF_B: Fq = field!(
        Fq,
        BigInteger768([
            0xf29a000000007ab6,
            0x8c391832e000739b,
            0x77738a6b6870f959,
            0xbe36179047832b03,
            0x84f3089e56574722,
            0xc5a3614ac0b1d984,
            0x5c81153f4906e9fe,
            0x4d28be3a9f55c815,
            0xd72c1d6f77d5f5c5,
            0x73a18e069ac04458,
            0xf9dfaa846595555f,
            0xd0f0a60a5be58c,
        ])
    );
    /// COFACTOR =
    /// 26642435879335816683987677701488073867751118270052650655942102502312977592501693353047140953112195348280268661194876
    const COFACTOR: &'static [u64] = &[
        0x3de580000000007c,
        0x832ba4061000003b,
        0xc61c554757551c0c,
        0xc856a0853c9db94c,
        0x2c77d5ac34cb12ef,
        0xad1972339049ce76,
    ];
    /// COFACTOR^(-1) mod r =
    /// 91141326767669940707819291241958318717982251277713150053234367522357946997763584490607453720072232540829942217804
    const COFACTOR_INV: Fr = field!(
        Fr,
        BigInteger384([
            489703175600125849,
            3883341943836920852,
            1678256062427438196,
            5848789333018172718,
            7127967896440782320,
            71512347676739162,
        ])
    );

    #[inline(always)]
    fn mul_by_a(_elem: &Self::BaseField) -> Self::BaseField {
        Self::BaseField::zero()
    }
}

///
/// G1_GENERATOR_X =
/// 3084896818094878465292814035026544910974143312995562714531210009417331019378722146056734617855323490417282419020353456806408059861474535810136628528514505922764873548629590004235442353333669842235683054328901866065961461891480718
///
/// See `snarkvm_algorithms::hash_to_curve::tests::bw6_761` for tests.
///
pub const G1_GENERATOR_X: Fq = field!(
    Fq,
    BigInteger768::new([
        10487806642818403143,
        10812021121647853028,
        6632345818060626684,
        563810138634848074,
        9992712565759626993,
        16673947229112731684,
        12352109620225751023,
        9268360244274824228,
        8492356566187285797,
        14499388366016474449,
        16934131622270447629,
        42721684071033164
    ])
);

///
/// G1_GENERATOR_Y =
/// 1722594430950431707034270778095718452934841892751405378948646210663260689333231099444985491480265568831760089926199287574304741119620587413810767542016852955943987284555845710626492919005786351909684459798008230268853750112996119
///
/// See `snarkvm_algorithms::hash_to_curve::tests::bw6_761` for tests.
///
pub const G1_GENERATOR_Y: Fq = field!(
    Fq,
    BigInteger768::new([
        12474383212032940380,
        12225017537866396465,
        12921956672179906606,
        10168973716825853592,
        422786365157830158,
        3613600924139080537,
        17090616832220632664,
        3609354759874489082,
        5622679152189666275,
        4843270626410357497,
        3757022585383056283,
        40431733580229529
    ])
);
