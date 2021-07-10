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
pub struct Bls12_377G2Parameters;

impl ModelParameters for Bls12_377G2Parameters {
    type BaseField = Fq;
    type ScalarField = Fr;
}

impl ShortWeierstrassParameters for Bls12_377G2Parameters {
    /// AFFINE_GENERATOR_COEFFS = (G2_GENERATOR_X, G2_GENERATOR_Y)
    const AFFINE_GENERATOR_COEFFS: (Self::BaseField, Self::BaseField) = (G2_GENERATOR_X, G2_GENERATOR_Y);
    /// COEFF_A = 0
    const COEFF_A: Fq = field!(Fq, BigInteger768([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]));
    /// COEFF_B = 4
    const COEFF_B: Fq = field!(
        Fq,
        BigInteger768([
            0x136efffffffe16c9,
            0x82cf5a6dcffe3319,
            0x6458c05f1f0e0741,
            0xd10ae605e52a4eda,
            0x41ca591c0266e100,
            0x7d0fd59c3626929f,
            0x9967dc004d00c112,
            0x1ccff9c033379af5,
            0x9ad6ec10a23f63af,
            0x5cec11251a72c235,
            0x8d18b1ae789ba83e,
            10403402007434220,
        ])
    );
    /// COFACTOR =
    /// 26642435879335816683987677701488073867751118270052650655942102502312977592501693353047140953112195348280268661194869
    const COFACTOR: &'static [u64] = &[
        0x3de5800000000075,
        0x832ba4061000003b,
        0xc61c554757551c0c,
        0xc856a0853c9db94c,
        0x2c77d5ac34cb12ef,
        0xad1972339049ce76,
    ];
    /// COFACTOR^(-1) mod r =
    /// 214911522365886453591244899095480747723790054550866810551297776298664428889000553861210287833206024638187939842124
    const COFACTOR_INV: Fr = field!(
        Fr,
        BigInteger384([
            14378295991815829998,
            14586153992421458638,
            9788477762582722914,
            12654821707953664524,
            15185631607604703397,
            26723985783783076,
        ])
    );

    #[inline(always)]
    fn mul_by_a(_elem: &Self::BaseField) -> Self::BaseField {
        Self::BaseField::zero()
    }
}

///
/// G2_GENERATOR_X =
///  1379824447046925053925803516826446813666959713660132146475377855840887530465700664266093320822990396082877604866921473089513727526853937217821005026837326271717122092248464798535668290526656694215408161034640476309747843577646970
///
/// See `snarkvm_algorithms::hash_to_curve::tests::bw6_761` for tests.
///
pub const G2_GENERATOR_X: Fq = field!(
    Fq,
    BigInteger768::new([
        11271109436428273038,
        16912618079138859072,
        18205656746276543019,
        980129637319460484,
        16668776315725772936,
        6504791895595261417,
        17672520696455642261,
        8125149140975696571,
        10978024769581152280,
        3667284036867981892,
        10946587263055511297,
        45766988980355617
    ])
);

///
/// G2_GENERATOR_Y =
/// 1050835022300138814583100651620759903348576607200595979410703998840829490733434315904240321139330355343841234020929419484656826745390468123520124426608430511537222419205835734084682075320421490148265889052675642775233610569345393
///
/// See `snarkvm_algorithms::hash_to_curve::tests::bw6_761` for tests.
///
pub const G2_GENERATOR_Y: Fq = field!(
    Fq,
    BigInteger768::new([
        2311811153969826608,
        6319969278718709871,
        1949674202653814605,
        11072586323700961766,
        10860963349504955895,
        13771794420622585590,
        4384007579317539118,
        10298178303616528479,
        7457846522035326759,
        2174851046759829336,
        14392023520391591144,
        25674968469810129
    ])
);
