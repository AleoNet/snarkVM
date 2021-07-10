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
/// 548300277143208370470678695366266429839120799927220954217122412131700072565385886272330413155172409119755953304536074890149359412851408456414505595462512752071492788194267343564981261358941753195544463428712608241091867757122460
///
/// See `snarkvm_algorithms::hash_to_curve::tests::bw6_761` for tests.
///
pub const G1_GENERATOR_X: Fq = field!(
    Fq,
    BigInteger768::new([
        1157171927825290318,
        3235954916956490670,
        16812058207263087357,
        10080996767888849283,
        2794842962193595859,
        2388739970221432725,
        3320012158242682795,
        7161314541864567281,
        13032933159384664301,
        13076100984012168483,
        7612495201479106839,
        53584131847326574
    ])
);

///
/// G1_GENERATOR_Y =
/// 3317472076756963306110108609744156196308178143114799958012980985496220654686731782787499145400398246050358757683997715518181197214027285759025659330708904762639837257598196509175335127695930298616567045490708432441379668097317972
///
/// See `snarkvm_algorithms::hash_to_curve::tests::bw6_761` for tests.
///
pub const G1_GENERATOR_Y: Fq = field!(
    Fq,
    BigInteger768::new([
        17537323669295701953,
        9286409947151450749,
        1543951643526860584,
        13597067073483526495,
        7544015345769907829,
        7005314844777489361,
        7007972873967911629,
        15155966061604017970,
        7045971538610474557,
        9672698377853857004,
        11582191816004119002,
        69728646693492388
    ])
);
