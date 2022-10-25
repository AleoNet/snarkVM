// Copyright (C) 2019-2022 Aleo Systems Inc.
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

use snarkvm_fields::{
    FftParameters,
    FieldParameters,
    Fp256,
    Fp256Parameters,
    PoseidonDefaultParameters,
    PoseidonDefaultParametersEntry,
};
use snarkvm_utilities::biginteger::BigInteger256 as BigInteger;

/// BLS12-377 scalar field.
///
/// Roots of unity computed from modulus and R using this sage code:
///
/// ```ignore
/// q = 8444461749428370424248824938781546531375899335154063827935233455917409239041
/// R = 6014086494747379908336260804527802945383293308637734276299549080986809532403 # Montgomery R
/// s = 47
/// o = q - 1
/// F = GF(q)
/// g = F.multiplicative_generator()
/// assert g.multiplicative_order() == o
/// g2 = g ** (o/2**s)
/// assert g2.multiplicative_order() == 2**s
/// def into_chunks(val, width, n):
///     return [int(int(val) // (2 ** (width * i)) % 2 ** width) for i in range(n)]
/// print("Gen (g % q): ", g % q)
/// print("Gen (g * R % q): ", g * R % q)
/// print("Gen into_chunks(g * R % q): ", into_chunks(g * R % q, 64, 4))
/// print("2-adic gen (g2 % q): ", g2 % q)
/// print("2-adic gen (g2 * R % q): ", g2 * R % q)
/// print("2-adic gen into_chunks(g2 * R % q): ", into_chunks(g2 * R % q, 64, 4))
/// ```
pub type Fr = Fp256<FrParameters>;

pub struct FrParameters;

impl Fp256Parameters for FrParameters {}

impl FftParameters for FrParameters {
    type BigInteger = BigInteger;

    #[rustfmt::skip]
    const POWERS_OF_G: &'static [BigInteger] = &[
        BigInteger([652114075796693467, 9243445511369889275, 4931911925841322402, 1202872507392441788]),
        BigInteger([357278320042854805, 8679756035718620602, 24147076532703075, 386601462669077701]),
        BigInteger([5821309058267914206, 930024428521638902, 15246330751380806139, 1156926535716486857]),
        BigInteger([2632950189532968238, 5392535751966509925, 4941032747320406800, 606661836792814885]),
        BigInteger([5797205653290972231, 12589652645565380589, 15756140458856054557, 1282965999660522983]),
        BigInteger([8306707692583858925, 7335440127635038484, 80047149603102519, 999419446928193801]),
        BigInteger([6956875524334552994, 13082051501117969572, 2938619391416456789, 304101838065490918]),
        BigInteger([3134783599327598467, 16631357106850039899, 2627692882553178120, 1024359273584097450]),
        BigInteger([12324015454749298429, 2042071882771645842, 7777946766613653260, 727393526865169839]),
        BigInteger([9072551969993762373, 557399396585981236, 17262240838654823200, 748448633583709418]),
        BigInteger([15745607881079653327, 10557409482890538181, 9754145699313741618, 1132312371963887010]),
        BigInteger([7370900649931229405, 15276690995798305716, 13935407585395225192, 182158718734875642]),
        BigInteger([6635723712198957876, 4459854046832330285, 2164992155939541098, 1061313009910823330]),
        BigInteger([9866347584304354950, 13633573028704785617, 1490634813024064211, 1193920255548692291]),
        BigInteger([12218842672787700946, 17502401118141046153, 3014192385295539746, 1278232049812798994]),
        BigInteger([12946324424558980416, 14730603725897097862, 9093296730287121559, 1301088483395017614]),
        BigInteger([13274457918106467667, 268045572525229395, 3096857327038933972, 791465315693154522]),
        BigInteger([3037126518913560865, 2335854563834671212, 1382087909526519297, 252291075014288680]),
        BigInteger([16107485408258731397, 1785252687040230207, 3542225586915910559, 939194661354943120]),
        BigInteger([9097289758579870090, 13453801755062728985, 5601243069208241633, 755137600292698783]),
        BigInteger([14650978806763043555, 1977920005064853667, 4380129240051161143, 696557356556620607]),
        BigInteger([17358176504781348191, 14494404166002030320, 6366857619701608749, 307359208841810046]),
        BigInteger([17831624937242459876, 3921541248490335982, 13076272174481132773, 203579329280294258]),
        BigInteger([4827811091337682419, 2252535990376301773, 4834246201427258736, 176594086007515430]),
        BigInteger([8224015011019235350, 3471968399227732089, 13945344924603372249, 63060411398793076]),
        BigInteger([3722182982532906157, 12487091451829240696, 15973379993919888494, 933622446976592570]),
        BigInteger([16918580269234120176, 9463814177789368183, 3230046188658025811, 700080667892842034]),
        BigInteger([5528995323364708964, 4645547136665772307, 10740406109497613416, 1060204339835393709]),
        BigInteger([9061129324622442628, 17862151211333623624, 184854872781714471, 22913953325058684]),
        BigInteger([15739313880441174300, 6790670340938497210, 3392071052049343159, 164706088673074561]),
        BigInteger([12245098422944482069, 9519432892459635938, 2900831850175999990, 1306683128084439414]),
        BigInteger([18170289470227336398, 7960339046993766714, 1786191937113318291, 974715431061307237]),
        BigInteger([14376073387189366589, 9083892742653733897, 7413368814740562107, 1229070466540458162]),
        BigInteger([5040906166828092920, 1597932116119946833, 17873658496853978081, 1121069752338197226]),
        BigInteger([3762856476273098914, 6524339332895362878, 17551910839959747290, 302725641766624789]),
        BigInteger([117129974372144763, 12585572440832662321, 11599001791804262972, 228386842112432103]),
        BigInteger([15180109745367336074, 4935483470718716768, 15393897344535774139, 138118718125512881]),
        BigInteger([9320622113425242802, 1507038136306394275, 6249837229555579558, 707827944913503007]),
        BigInteger([8510091037240551326, 2255407371696257485, 9086980551808272394, 1151908693325144507]),
        BigInteger([8197034620141798687, 4334208919548785209, 13603393822593628560, 479050288045546609]),
        BigInteger([6310980340485637787, 4470469036336467487, 10811712561993161098, 358887687171593677]),
        BigInteger([1532731303765601343, 7737984259716464239, 18210871776416574727, 1086801557967392038]),
        BigInteger([8069388237560588236, 1260332170967911028, 13997795246790076617, 325648630152787926]),
        BigInteger([14375636960200474030, 3537274190141887733, 721323736305227360, 1057644659207653462]),
        BigInteger([1117754170585778689, 2375847183000234400, 8144967840909054003, 522520945354137089]),
        BigInteger([10311624665562349569, 14944710915545628673, 2588746559005780992, 0]),
    ];
    #[rustfmt::skip]
    const TWO_ADICITY: u32 = 47;
    /// TWO_ADIC_ROOT_OF_UNITY = 8065159656716812877374967518403273466521432693661810619979959746626482506078
    /// Encoded in Montgomery form, the value is
    /// (8065159656716812877374967518403273466521432693661810619979959746626482506078 * R % q) =
    /// 7039866554349711480672062101017509031917008525101396696252683426045173093960
    #[rustfmt::skip]
    const TWO_ADIC_ROOT_OF_UNITY: BigInteger = BigInteger([
        12646347781564978760u64,
        6783048705277173164u64,
        268534165941069093u64,
        1121515446318641358u64,
    ]);
}

impl FieldParameters for FrParameters {
    #[rustfmt::skip]
    const CAPACITY: u32 = Self::MODULUS_BITS - 1;
    /// GENERATOR = 22
    /// Encoded in Montgomery form, so the value is
    /// (22 * R) % q = 5642976643016801619665363617888466827793962762719196659561577942948671127251
    #[rustfmt::skip]
    const GENERATOR: BigInteger = BigInteger([
        2984901390528151251u64,
        10561528701063790279u64,
        5476750214495080041u64,
        898978044469942640u64,
    ]);
    #[rustfmt::skip]
    const INV: u64 = 725501752471715839u64;
    /// MODULUS = 8444461749428370424248824938781546531375899335154063827935233455917409239041
    #[rustfmt::skip]
    const MODULUS: BigInteger = BigInteger([
        725501752471715841u64,
        6461107452199829505u64,
        6968279316240510977u64,
        1345280370688173398u64,
    ]);
    #[rustfmt::skip]
    const MODULUS_BITS: u32 = 253;
    /// (r - 1)/2 =
    /// 4222230874714185212124412469390773265687949667577031913967616727958704619520
    #[rustfmt::skip]
    const MODULUS_MINUS_ONE_DIV_TWO: BigInteger = BigInteger([
        0x8508c00000000000,
        0xacd53b7f68000000,
        0x305a268f2e1bd800,
        0x955b2af4d1652ab,
    ]);
    #[rustfmt::skip]
    const R: BigInteger = BigInteger([
        9015221291577245683u64,
        8239323489949974514u64,
        1646089257421115374u64,
        958099254763297437u64,
    ]);
    #[rustfmt::skip]
    const R2: BigInteger = BigInteger([
        2726216793283724667u64,
        14712177743343147295u64,
        12091039717619697043u64,
        81024008013859129u64,
    ]);
    #[rustfmt::skip]
    const REPR_SHAVE_BITS: u32 = 3;
    // T and T_MINUS_ONE_DIV_TWO, where r - 1 = 2^s * t

    /// t = (r - 1) / 2^s =
    /// 60001509534603559531609739528203892656505753216962260608619555
    #[rustfmt::skip]
    const T: BigInteger = BigInteger([
        0xedfda00000021423,
        0x9a3cb86f6002b354,
        0xcabd34594aacc168,
        0x2556,
    ]);
    /// (t - 1) / 2 =
    /// 30000754767301779765804869764101946328252876608481130304309777
    #[rustfmt::skip]
    const T_MINUS_ONE_DIV_TWO: BigInteger = BigInteger([
        0x76fed00000010a11,
        0x4d1e5c37b00159aa,
        0x655e9a2ca55660b4,
        0x12ab,
    ]);
}

impl PoseidonDefaultParameters for FrParameters {
    const PARAMS_OPT_FOR_CONSTRAINTS: [PoseidonDefaultParametersEntry; 7] = [
        PoseidonDefaultParametersEntry::new(2, 17, 8, 31, 0),
        PoseidonDefaultParametersEntry::new(3, 17, 8, 31, 0),
        PoseidonDefaultParametersEntry::new(4, 17, 8, 31, 0),
        PoseidonDefaultParametersEntry::new(5, 17, 8, 31, 0),
        PoseidonDefaultParametersEntry::new(6, 17, 8, 31, 0),
        PoseidonDefaultParametersEntry::new(7, 17, 8, 31, 0),
        PoseidonDefaultParametersEntry::new(8, 17, 8, 31, 0),
    ];
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_fields::{Field, PrimeField};

    #[test]
    fn test_powers_of_g() {
        let two = Fr::from(2u8);

        // Compute the expected powers of G.
        let g = Fr::from_bigint(FrParameters::GENERATOR).unwrap().pow(FrParameters::T);
        let powers = (0..FrParameters::TWO_ADICITY - 1)
            .map(|i| g.pow(two.pow(Fr::from(i as u64).to_bigint()).to_bigint()).to_bigint())
            .collect::<Vec<_>>();

        // Ensure the correct number of powers of G are present.
        assert_eq!(FrParameters::POWERS_OF_G.len() as u64, (FrParameters::TWO_ADICITY - 1) as u64);
        assert_eq!(FrParameters::POWERS_OF_G.len(), powers.len());

        // Ensure the expected and candidate powers match.
        for (expected, candidate) in powers.iter().zip(FrParameters::POWERS_OF_G.iter()) {
            println!("{:?} =?= {:?}", expected, candidate);
            assert_eq!(expected, candidate);
        }
    }
}
