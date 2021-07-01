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

use snarkvm_fields::{FftParameters, FieldParameters, Fp384, Fp384Parameters, PoseidonMDSParameters};
use snarkvm_utilities::biginteger::BigInteger384 as BigInteger;

pub type Fq = Fp384<FqParameters>;

pub struct FqParameters;

impl Fp384Parameters for FqParameters {}

impl FftParameters for FqParameters {
    type BigInteger = BigInteger;

    #[rustfmt::skip]
    const TWO_ADICITY: u32 = 46u32;
    #[rustfmt::skip]
    const TWO_ADIC_ROOT_OF_UNITY: BigInteger = BigInteger([
        2022196864061697551u64,
        17419102863309525423u64,
        8564289679875062096u64,
        17152078065055548215u64,
        17966377291017729567u64,
        68610905582439508u64,
    ]);
}

impl FieldParameters for FqParameters {
    #[rustfmt::skip]
    const CAPACITY: u32 = Self::MODULUS_BITS - 1;
    /// GENERATOR = -5
    #[rustfmt::skip]
    const GENERATOR: BigInteger = BigInteger([
        0xfc0b8000000002fa,
        0x97d39cf6e000018b,
        0x2072420fbfa05044,
        0xcbbcbd50d97c3802,
        0xbaf1ec35813f9eb,
        0x9974a2c0945ad2,
    ]);
    #[rustfmt::skip]
    const INV: u64 = 9586122913090633727u64;
    /// MODULUS = 258664426012969094010652733694893533536393512754914660539884262666720468348340822774968888139573360124440321458177
    #[rustfmt::skip]
    const MODULUS: BigInteger = BigInteger([
        0x8508c00000000001,
        0x170b5d4430000000,
        0x1ef3622fba094800,
        0x1a22d9f300f5138f,
        0xc63b05c06ca1493b,
        0x1ae3a4617c510ea,
    ]);
    #[rustfmt::skip]
    const MODULUS_BITS: u32 = 377;
    #[rustfmt::skip]
    const MODULUS_MINUS_ONE_DIV_TWO: BigInteger = BigInteger([
        0x4284600000000000,
        0xb85aea218000000,
        0x8f79b117dd04a400,
        0x8d116cf9807a89c7,
        0x631d82e03650a49d,
        0xd71d230be28875,
    ]);
    #[rustfmt::skip]
    const R: BigInteger = BigInteger([
        202099033278250856u64,
        5854854902718660529u64,
        11492539364873682930u64,
        8885205928937022213u64,
        5545221690922665192u64,
        39800542322357402u64,
    ]);
    #[rustfmt::skip]
    const R2: BigInteger = BigInteger([
        0xb786686c9400cd22,
        0x329fcaab00431b1,
        0x22a5f11162d6b46d,
        0xbfdf7d03827dc3ac,
        0x837e92f041790bf9,
        0x6dfccb1e914b88,
    ]);
    #[rustfmt::skip]
    const REPR_SHAVE_BITS: u32 = 7;
    // T and T_MINUS_ONE_DIV_TWO, where MODULUS - 1 = 2^S * T

    /// T = (MODULUS - 1) // 2^S =
    /// 3675842578061421676390135839012792950148785745837396071634149488243117337281387659330802195819009059
    #[rustfmt::skip]
    const T: BigInteger = BigInteger([
        0x7510c00000021423,
        0x88bee82520005c2d,
        0x67cc03d44e3c7bcd,
        0x1701b28524ec688b,
        0xe9185f1443ab18ec,
        0x6b8,
    ]);
    /// (T - 1) // 2 =
    /// 1837921289030710838195067919506396475074392872918698035817074744121558668640693829665401097909504529
    #[rustfmt::skip]
    const T_MINUS_ONE_DIV_TWO: BigInteger = BigInteger([
        0xba88600000010a11,
        0xc45f741290002e16,
        0xb3e601ea271e3de6,
        0xb80d94292763445,
        0x748c2f8a21d58c76,
        0x35c,
    ]);
}

impl PoseidonMDSParameters for FqParameters {
    const POSEIDON_ALPHA: u64 = 31;
    const POSEIDON_FULL_ROUNDS: u32 = 8;
    const POSEIDON_MDS: [[BigInteger; 3]; 3] = [
        [
            BigInteger([
                16761615102818334957u64,
                12482138038048699934u64,
                3817096965469984601u64,
                6989969318858031733u64,
                3576610594321980885u64,
                36490137127210368u64,
            ]),
            BigInteger([
                9566144474383830910u64,
                11150426687430544949u64,
                16331460408238788351u64,
                2005897529228708767u64,
                3062046737096295036u64,
                63140901972144186u64,
            ]),
            BigInteger([
                667196415962656604u64,
                8983143523464838295u64,
                1678573521440382262u64,
                2229888761407573441u64,
                10012085227077399162u64,
                117093948091414363u64,
            ]),
        ],
        [
            BigInteger([
                13587048708902679877u64,
                8286394602935866198u64,
                14019498734289822666u64,
                3540135739465249599u64,
                4432355063077857820u64,
                3619990303674074u64,
            ]),
            BigInteger([
                14778968494591858924u64,
                6237379533604742896u64,
                7747224932072259059u64,
                7156068636969940628u64,
                7832220824164838569u64,
                98958126183981927u64,
            ]),
            BigInteger([
                5004312693389915478u64,
                3300178519609569861u64,
                13640583711772033155u64,
                4476271394341818444u64,
                15970828387942405354u64,
                105191205674577396u64,
            ]),
        ],
        [
            BigInteger([
                12771785550679526545u64,
                6478226502717735083u64,
                15595525529283996344u64,
                4618245953347533529u64,
                10574461518149736257u64,
                75849574116268738u64,
            ]),
            BigInteger([
                15297186288394220678u64,
                11433282922109160880u64,
                17320311942882946516u64,
                7132752839720018915u64,
                8433945621090238516u64,
                62317511368563555u64,
            ]),
            BigInteger([
                81416247066316724u64,
                14874796636981620039u64,
                6911864355757151549u64,
                13271831832425350370u64,
                17068699463819752399u64,
                115990511609677769u64,
            ]),
        ],
    ];
    const POSEIDON_PARTIAL_ROUNDS: u32 = 24;
}
