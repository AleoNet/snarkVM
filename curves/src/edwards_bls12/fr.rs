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

use snarkvm_fields::{FftParameters, FieldParameters, Fp256, Fp256Parameters, PoseidonMDSParameters};
use snarkvm_utilities::biginteger::BigInteger256 as BigInteger;

pub type Fr = Fp256<FrParameters>;

pub struct FrParameters;

impl Fp256Parameters for FrParameters {}

impl FftParameters for FrParameters {
    type BigInteger = BigInteger;

    const TWO_ADICITY: u32 = 1;
    #[rustfmt::skip]
    const TWO_ADIC_ROOT_OF_UNITY: BigInteger = BigInteger([
        15170730761708361161u64,
        13670723686578117817u64,
        12803492266614043665u64,
        50861023252832611u64,
    ]);
}

impl FieldParameters for FrParameters {
    #[rustfmt::skip]
    const CAPACITY: u32 = Self::MODULUS_BITS - 1;
    /// 70865795004005329077606947863872807680085016823885970091001235374859923341923
    #[rustfmt::skip]
    const GENERATOR: BigInteger = BigInteger([
        11289572479685143826u64,
        11383637369941080925u64,
        2288212753973340071u64,
        82014976407880291u64,
    ]);
    #[rustfmt::skip]
    const INV: u64 = 9659935179256617473u64;
    /// MODULUS = 2111115437357092606062206234695386632838870926408408195193685246394721360383
    #[rustfmt::skip]
    const MODULUS: BigInteger = BigInteger([
        13356249993388743167u64,
        5950279507993463550u64,
        10965441865914903552u64,
        336320092672043349u64,
    ]);
    #[rustfmt::skip]
    const MODULUS_BITS: u32 = 251;
    #[rustfmt::skip]
    const MODULUS_MINUS_ONE_DIV_TWO: BigInteger = BigInteger([
        6678124996694371583u64,
        2975139753996731775u64,
        14706092969812227584u64,
        168160046336021674u64,
    ]);
    #[rustfmt::skip]
    const R: BigInteger = BigInteger([
        16632263305389933622u64,
        10726299895124897348u64,
        16608693673010411502u64,
        285459069419210737u64,
    ]);
    #[rustfmt::skip]
    const R2: BigInteger = BigInteger([
        3987543627614508126u64,
        17742427666091596403u64,
        14557327917022607905u64,
        322810149704226881u64,
    ]);
    #[rustfmt::skip]
    const REPR_SHAVE_BITS: u32 = 5;
    #[rustfmt::skip]
    const T: BigInteger = BigInteger([
        6678124996694371583,
        2975139753996731775,
        14706092969812227584,
        168160046336021674
    ]);
    #[rustfmt::skip]
    const T_MINUS_ONE_DIV_TWO: BigInteger = BigInteger([
        12562434535201961599,
        1487569876998365887,
        7353046484906113792,
        84080023168010837
    ]);
}

impl PoseidonMDSParameters for FrParameters {
    const POSEIDON_ALPHA: u64 = 31;
    const POSEIDON_FULL_ROUNDS: u32 = 8;
    const POSEIDON_MDS: [[Self::BigInteger; 3]; 3] = [
        [
            BigInteger([
                13931651401159535461u64,
                6006477131456032335u64,
                8861043438808324862u64,
                239206041950301407u64,
            ]),
            BigInteger([
                14599526219703300833u64,
                2165591283025862387u64,
                3262244481033513448u64,
                254007036298939783u64,
            ]),
            BigInteger([
                18398064082861167311u64,
                7936119269837814119u64,
                16409634246018729623u64,
                113093337369522454u64,
            ]),
        ],
        [
            BigInteger([
                1380331091829797739u64,
                3917551297481786153u64,
                18371229596600745376u64,
                76132760663693379u64,
            ]),
            BigInteger([
                5360216235499494221u64,
                5637426667709928538u64,
                11157148077451652763u64,
                35812199642490000u64,
            ]),
            BigInteger([
                3509088436533735732u64,
                2584527352917660841u64,
                5432587255857104503u64,
                202059883065894434u64,
            ]),
        ],
        [
            BigInteger([
                14942267501094948442u64,
                17954062856329404331u64,
                8245645794667695156u64,
                262464923933281526u64,
            ]),
            BigInteger([
                12976280035124916000u64,
                11216467143489102861u64,
                2382044689775017229u64,
                156401286093210198u64,
            ]),
            BigInteger([
                10657872451498634033u64,
                5777972321481254942u64,
                16770446898451849249u64,
                88790146008022152u64,
            ]),
        ],
    ];
    const POSEIDON_PARTIAL_ROUNDS: u32 = 24;
}
