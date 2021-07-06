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

pub type Fr = Fp384<FrParameters>;

pub struct FrParameters;

impl Fp384Parameters for FrParameters {}

impl FftParameters for FrParameters {
    type BigInteger = BigInteger;

    const TWO_ADICITY: u32 = 2u32;
    #[rustfmt::skip]
    const TWO_ADIC_ROOT_OF_UNITY: BigInteger = BigInteger([
        12119792640622387781u64,
        8318439284650634613u64,
        6931324077796168275u64,
        12851391603681523141u64,
        6881015057611215092u64,
        1893962574900431u64,
    ]);
}

impl FieldParameters for FrParameters {
    #[rustfmt::skip]
    const CAPACITY: u32 = Self::MODULUS_BITS - 1;
    /// 2
    #[rustfmt::skip]
    const GENERATOR: BigInteger = BigInteger([
        1999556893213776791u64,
        13750542494830678672u64,
        1782306145063399878u64,
        452443773434042853u64,
        15997990832658725900u64,
        3914639203155617u64,
    ]);
    #[rustfmt::skip]
    const INV: u64 = 16242011933465909059u64;
    /// MODULUS = 32333053251621136751331591711861691692049189094364332567435817881934511297123972799646723302813083835942624121493
    #[rustfmt::skip]
    const MODULUS: BigInteger = BigInteger([
        4684667634276979349u64,
        3748803659444032385u64,
        16273581227874629698u64,
        7152942431629910641u64,
        6397188139321141543u64,
        15137289088311837u64,
    ]);
    #[rustfmt::skip]
    const MODULUS_BITS: u32 = 374;
    #[rustfmt::skip]
    const MODULUS_MINUS_ONE_DIV_TWO: BigInteger = BigInteger([
        11565705853993265482u64,
        1874401829722016192u64,
        17360162650792090657u64,
        12799843252669731128u64,
        12421966106515346579u64,
        7568644544155918u64,
    ]);
    #[rustfmt::skip]
    const R: BigInteger = BigInteger([
        12565484300600153878u64,
        8749673077137355528u64,
        9027943686469014788u64,
        13026065139386752555u64,
        11197589485989933721u64,
        9525964145733727u64,
    ]);
    #[rustfmt::skip]
    const R2: BigInteger = BigInteger([
        17257035094703902127u64,
        16096159112880350050u64,
        3498553494623421763u64,
        333405339929360058u64,
        1125865524035793947u64,
        1586246138566285u64,
    ]);
    #[rustfmt::skip]
    const REPR_SHAVE_BITS: u32 = 10;
    #[rustfmt::skip]
    const T: BigInteger = BigInteger([
        5782852926996632741,
        10160572951715783904,
        8680081325396045328,
        15623293663189641372,
        6210983053257673289,
        3784322272077959
    ]);
    #[rustfmt::skip]
    const T_MINUS_ONE_DIV_TWO: BigInteger = BigInteger([
        2891426463498316370,
        5080286475857891952,
        4340040662698022664,
        17035018868449596494,
        12328863563483612452,
        1892161136038979
    ]);
}

impl PoseidonMDSParameters for FrParameters {
    const POSEIDON_ALPHA: u64 = 31;
    const POSEIDON_FULL_ROUNDS: u32 = 8;
    const POSEIDON_MDS: [[Self::BigInteger; 3]; 3] = [
        [
            BigInteger([
                17217954060589444817u64,
                18133363521130456075u64,
                10652608982548728377u64,
                11908238962889374165u64,
                10207510272304346855u64,
                4361090771298045u64,
            ]),
            BigInteger([
                9789765500825557069u64,
                3954475707654511974u64,
                6562178006979829515u64,
                10572999003868849006u64,
                3676837079995727337u64,
                10933639034085319u64,
            ]),
            BigInteger([
                5247306120115791987u64,
                5691280391474474389u64,
                5126347947307459368u64,
                2780849223932391093u64,
                4785035953196725568u64,
                2789802665678719u64,
            ]),
        ],
        [
            BigInteger([
                17132810200199329200u64,
                11471619601481689281u64,
                8288684216025418414u64,
                13400402597530152287u64,
                17618174483447679472u64,
                355041645621293u64,
            ]),
            BigInteger([
                13793860387565917855u64,
                15620226780795009337u64,
                10134532400816811136u64,
                13361716890246139480u64,
                8864343217517711966u64,
                13398876945412417u64,
            ]),
            BigInteger([
                5836783721513452851u64,
                8352837549236734011u64,
                16435455469483394269u64,
                5669360887676956106u64,
                5686903230478167750u64,
                2130105905405189u64,
            ]),
        ],
        [
            BigInteger([
                10170299749750010274u64,
                2582497041753250789u64,
                6676689891856248351u64,
                3628549153682438098u64,
                6962296203140356292u64,
                1974903442171078u64,
            ]),
            BigInteger([
                7718122081580912208u64,
                14011594674477349124u64,
                3870296720504221781u64,
                16387814393955397318u64,
                10158182266192082236u64,
                12852702065674508u64,
            ]),
            BigInteger([
                4221838557285273639u64,
                617109266713395115u64,
                13582951657279832754u64,
                3175636364870701441u64,
                7935437062923434981u64,
                2361882315280222u64,
            ]),
        ],
    ];
    const POSEIDON_PARTIAL_ROUNDS: u32 = 24;
}
