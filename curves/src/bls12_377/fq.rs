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
    const POSEIDON_ALPHA: u64 = 17;
    const POSEIDON_FULL_ROUNDS: u32 = 8;
    const POSEIDON_MDS: [[BigInteger; 3]; 3] = [
        [
            BigInteger([
                8172967597780954035u64,
                6008815347824693113u64,
                4592403753008098902u64,
                14851063508046765924u64,
                5306993576991644926u64,
                16603003293726031u64,
            ]),
            BigInteger([
                17569403088604308u64,
                17682572356524644437u64,
                2359184719407488192u64,
                16083283379166159201u64,
                5105602493841543119u64,
                8672980712485792u64,
            ]),
            BigInteger([
                12316216836904703884u64,
                17783819148460676477u64,
                5182093414834056284u64,
                9192323074044742792u64,
                15091267172548134993u64,
                45090915910082212u64,
            ]),
        ],
        [
            BigInteger([
                14801833939635027068u64,
                7013328969900695617u64,
                15720484090102208943u64,
                13671746346006573204u64,
                17925411853826579348u64,
                86428814309121125u64,
            ]),
            BigInteger([
                17624342405307035836u64,
                6116808379636279617u64,
                10799701812362080479u64,
                10006225831313738853u64,
                6470237557205326410u64,
                79199972292541975u64,
            ]),
            BigInteger([
                3054733087357147792u64,
                17691235172212186961u64,
                8334009145457048575u64,
                12262622436410632068u64,
                2349412626666515315u64,
                11319001813360516u64,
            ]),
        ],
        [
            BigInteger([
                2273528872882178312u64,
                16665688939646869132u64,
                341033436731129471u64,
                1114340925258231644u64,
                16154103318641537191u64,
                8065793780653267u64,
            ]),
            BigInteger([
                4629876387047989026u64,
                2210105303418988442u64,
                16069385238970284835u64,
                6570780206775703383u64,
                17759700008175431301u64,
                16439019728427980u64,
            ]),
            BigInteger([
                12717129937993317565u64,
                13426457888220300229u64,
                5221551723056385617u64,
                6256493013794088213u64,
                461901669955011041u64,
                105694585219148878u64,
            ]),
        ],
    ];
    const POSEIDON_PARTIAL_ROUNDS: u32 = 31;
}
