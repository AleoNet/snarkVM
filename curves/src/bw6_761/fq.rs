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

use snarkvm_fields::{FftParameters, FieldParameters, Fp768, Fp768Parameters, PoseidonMDSParameters};
use snarkvm_utilities::biginteger::BigInteger768 as BigInteger;

pub type Fq = Fp768<FqParameters>;

pub struct FqParameters;

impl Fp768Parameters for FqParameters {}

impl FftParameters for FqParameters {
    type BigInteger = BigInteger;

    // The internal representation of this type is six 64-bit unsigned
    // integers in little-endian order. Values are always in
    // Montgomery form; i.e., Scalar(a) = aR mod p, with R=2^768.

    /// (MODULUS - 1) % 2^TWO_ADICITY == 0
    #[rustfmt::skip]
    const TWO_ADICITY: u32 = 1;
    /// least_quadratic_nonresidue(MODULUS) in Sage.
    #[rustfmt::skip]
    const TWO_ADIC_ROOT_OF_UNITY: BigInteger = BigInteger([
        17481284903592032950u64,
        10104133845767975835u64,
        8607375506753517913u64,
        13706168424391191299u64,
        9580010308493592354u64,
        14241333420363995524u64,
        6665632285037357566u64,
        5559902898979457045u64,
        15504799981718861253u64,
        8332096944629367896u64,
        18005297320867222879u64,
        58811391084848524u64,
    ]);
}

impl FieldParameters for FqParameters {
    #[rustfmt::skip]
    const CAPACITY: u32 = Self::MODULUS_BITS - 1;
    /// GENERATOR = 2
    /// primitive_root(MODULUS)
    #[rustfmt::skip]
    const GENERATOR: BigInteger = BigInteger([
        289919226011913130u64,
        13019990545710127566u64,
        4409829457611675068u64,
        13030600802816293865u64,
        15696054586628993047u64,
        9353078419867322391u64,
        5664203968291172875u64,
        5090703637405909511u64,
        17774776443174359288u64,
        10018561694451762270u64,
        12632664537138156478u64,
        46143195394855163u64,
    ]);
    /// (-1/MODULUS) % 2^64
    #[rustfmt::skip]
    const INV: u64 = 744663313386281181u64;
    /// MODULUS = 6891450384315732539396789682275657542479668912536150109513790160209623422243491736087683183289411687640864567753786613451161759120554247759349511699125301598951605099378508850372543631423596795951899700429969112842764913119068299
    #[rustfmt::skip]
    const MODULUS: BigInteger = BigInteger([
        0xf49d00000000008b,
        0xe6913e6870000082,
        0x160cf8aeeaf0a437,
        0x98a116c25667a8f8,
        0x71dcd3dc73ebff2e,
        0x8689c8ed12f9fd90,
        0x03cebaff25b42304,
        0x707ba638e584e919,
        0x528275ef8087be41,
        0xb926186a81d14688,
        0xd187c94004faff3e,
        0x122e824fb83ce0a,
    ]);
    #[rustfmt::skip]
    const MODULUS_BITS: u32 = 761;
    /// (MODULUS - 1) / 2
    #[rustfmt::skip]
    const MODULUS_MINUS_ONE_DIV_TWO: BigInteger = BigInteger([
        0x7a4e800000000045,
        0xf3489f3438000041,
        0x0b067c577578521b,
        0x4c508b612b33d47c,
        0x38ee69ee39f5ff97,
        0x4344e476897cfec8,
        0x81e75d7f92da1182,
        0xb83dd31c72c2748c,
        0x29413af7c043df20,
        0x5c930c3540e8a344,
        0x68c3e4a0027d7f9f,
        0x9174127dc1e705,
    ]);
    /// 2^768 % MODULUS
    #[rustfmt::skip]
    const R: BigInteger = BigInteger([
        144959613005956565u64,
        6509995272855063783u64,
        11428286765660613342u64,
        15738672438262922740u64,
        17071399330169272331u64,
        13899911246788437003u64,
        12055474021000362245u64,
        2545351818702954755u64,
        8887388221587179644u64,
        5009280847225881135u64,
        15539704305423854047u64,
        23071597697427581u64,
    ]);
    /// R^2
    #[rustfmt::skip]
    const R2: BigInteger = BigInteger([
        14305184132582319705u64,
        8868935336694416555u64,
        9196887162930508889u64,
        15486798265448570248u64,
        5402985275949444416u64,
        10893197322525159598u64,
        3204916688966998390u64,
        12417238192559061753u64,
        12426306557607898622u64,
        1305582522441154384u64,
        10311846026977660324u64,
        48736111365249031u64,
    ]);
    /// Gap to 64-bit machine word
    #[rustfmt::skip]
    const REPR_SHAVE_BITS: u32 = 7;
    /// T =
    /// 3445725192157866269698394841137828771239834456268075054756895080104811711121745868043841591644705843820432283876893306725580879560277123879674755849562650799475802549689254425186271815711798397975949850214984556421382456559534149
    /// (MODULUS - 1) / 2 ^ TWO_ADICITY
    #[rustfmt::skip]
    const T: BigInteger = BigInteger([
        0x7a4e800000000045,
        0xf3489f3438000041,
        0x0b067c577578521b,
        0x4c508b612b33d47c,
        0x38ee69ee39f5ff97,
        0x4344e476897cfec8,
        0x81e75d7f92da1182,
        0xb83dd31c72c2748c,
        0x29413af7c043df20,
        0x5c930c3540e8a344,
        0x68c3e4a0027d7f9f,
        0x9174127dc1e705,
    ]);
    /// (T - 1)/2 =
    /// 1722862596078933134849197420568914385619917228134037527378447540052405855560872934021920795822352921910216141938446653362790439780138561939837377924781325399737901274844627212593135907855899198987974925107492278210691228279767074
    #[rustfmt::skip]
    const T_MINUS_ONE_DIV_TWO: BigInteger = BigInteger([
        0xbd27400000000022,
        0xf9a44f9a1c000020,
        0x05833e2bbabc290d,
        0xa62845b09599ea3e,
        0x1c7734f71cfaffcb,
        0x21a2723b44be7f64,
        0x40f3aebfc96d08c1,
        0x5c1ee98e39613a46,
        0x14a09d7be021ef90,
        0xae49861aa07451a2,
        0xb461f250013ebfcf,
        0x48ba093ee0f382,
    ]);
}

impl PoseidonMDSParameters for FqParameters {
    const POSEIDON_ALPHA: u64 = 17;
    const POSEIDON_FULL_ROUNDS: u32 = 8;
    const POSEIDON_MDS: [[Self::BigInteger; 3]; 3] = [
        [
            BigInteger([
                10743229428991736264u64,
                10448316589208720160u64,
                14505148679008277519u64,
                15957707643993762172u64,
                2431956304676530844u64,
                16596203368949874139u64,
                4040992394601396798u64,
                9571359464926971458u64,
                4988811053211852817u64,
                18120011064639762889u64,
                3438151399094510058u64,
                8608064606098966u64,
            ]),
            BigInteger([
                2459903778820384158u64,
                3425345116710753933u64,
                1430237987210590153u64,
                520502621671042041u64,
                16970231401222405771u64,
                4292694408198139836u64,
                5952866738002346245u64,
                649630761146651354u64,
                2897499763589695769u64,
                7703684679442486833u64,
                17377938511930111922u64,
                15497963714008725u64,
            ]),
            BigInteger([
                11021962663494259726u64,
                3202318270926620729u64,
                14177961840228808226u64,
                14055905176848061034u64,
                938009033099217421u64,
                295085601195194819u64,
                817808458523855310u64,
                1816190372176726176u64,
                9284699149487646243u64,
                1446373780403310083u64,
                8592620084450211298u64,
                53901825861024384u64,
            ]),
        ],
        [
            BigInteger([
                13239212393053111607u64,
                647064997675168928u64,
                2297640044677556156u64,
                2239161087329331326u64,
                12242833074543173934u64,
                6619581982443464988u64,
                4973100030105253508u64,
                11829108334843818457u64,
                7656968258795122496u64,
                5485589333820198458u64,
                15093948133930556930u64,
                13003828487101132u64,
            ]),
            BigInteger([
                9161659543148111335u64,
                12001676319887188662u64,
                16766463534802982158u64,
                16683566776410052572u64,
                10269311358336180044u64,
                16446947541404696936u64,
                15880320525346811627u64,
                10540261286979378049u64,
                413369686751523294u64,
                4462569890837314447u64,
                13573202539440199086u64,
                44516192315261280u64,
            ]),
            BigInteger([
                11689863850420338082u64,
                10262874029280379830u64,
                2872268007428373621u64,
                15357764026913606086u64,
                12477023820012360679u64,
                1808368672998022296u64,
                4402887219516110827u64,
                10390688075458945428u64,
                7693362028604007787u64,
                10129772415796140346u64,
                15540567672696440373u64,
                12698047507430083u64,
            ]),
        ],
        [
            BigInteger([
                10765801007952212046u64,
                18140517522314726781u64,
                2558780518052614414u64,
                7961054827347053253u64,
                9243315203405009264u64,
                5075276458022990986u64,
                9608713924863654342u64,
                9797042053087848217u64,
                12567606532504551341u64,
                17305375105582946707u64,
                10648945149364874319u64,
                35472936185172755u64,
            ]),
            BigInteger([
                695370516733055533u64,
                14872260196474781761u64,
                13992062235576720144u64,
                6150385733659080771u64,
                16251372483060837289u64,
                16808698490905032343u64,
                17036768170524264429u64,
                12571384330206392965u64,
                10184376158645418868u64,
                5388544683330612653u64,
                12517478907228807416u64,
                54026167893061646u64,
            ]),
            BigInteger([
                10348711396174898086u64,
                7778944623213880452u64,
                7694983968757142097u64,
                16447794964603215849u64,
                1048128980493097090u64,
                3921463359492927543u64,
                1351294200481077199u64,
                9142066744286438934u64,
                3500526922528480353u64,
                1909160669132565337u64,
                15184084382755246091u64,
                12232120465797277u64,
            ]),
        ],
    ];
    const POSEIDON_PARTIAL_ROUNDS: u32 = 31;
}
