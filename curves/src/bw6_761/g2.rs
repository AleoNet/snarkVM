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
///  12396641805492461664047944547716626246622726413716325514578855015708751941073354605391144730949906058792699340873351761792275567434439857256502535718512012900825516349253359648697192702793852676897460477790268766996191561426115
///
/// See `snarkvm_algorithms::hash_to_curve::tests::bw6_761` for tests.
///
pub const G2_GENERATOR_X: Fq = field!(
    Fq,
    BigInteger768::new([
        13965385169003496293,
        15426759243192778648,
        17412803276392918350,
        17892104412223195454,
        7532942519447222464,
        11305536108286109734,
        13853093656533611357,
        3285564323678932468,
        9915794714252477034,
        3414216529059533261,
        11265573112366039784,
        5978735415715022
    ])
);

///
/// G2_GENERATOR_Y =
/// 3307524539084980175348192287168406817851662089289532346813191207846857431628300288777230178426528997214653383965949568784001180902638452916442590352134990654138684202694553699651807581643537139768612814360134519690660810904199476
///
/// See `snarkvm_algorithms::hash_to_curve::tests::bw6_761` for tests.
///
pub const G2_GENERATOR_Y: Fq = field!(
    Fq,
    BigInteger768::new([
        122961968395967336,
        12501821910101597401,
        9993203793787452378,
        9589026370105636356,
        207488117621663087,
        18200370713322471620,
        17356725932671146122,
        18337093169776622661,
        3372949398219407920,
        12781993496907152533,
        16711250998472995857,
        20967738953282646
    ])
);
