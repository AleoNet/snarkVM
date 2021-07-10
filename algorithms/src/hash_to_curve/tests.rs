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

#[cfg(test)]
mod bls12_377 {
    use crate::hash_to_curve::{hash_to_curve, try_hash_to_curve};
    use snarkvm_curves::{
        bls12_377::{G1Affine, G2Affine},
        AffineCurve,
    };
    use snarkvm_fields::PrimeField;
    use snarkvm_utilities::{BigInteger384, ConstantSerializedSize};

    #[test]
    fn hash_bls12_377_g1() {
        let g1 = hash_to_curve::<G1Affine, 48>("Aleo BLS12-377 G1 in 1").unwrap();
        assert!(g1.is_on_curve());
        assert!(g1.is_in_correct_subgroup_assuming_on_curve());
        assert_eq!(G1Affine::SERIALIZED_SIZE, 384 / 8);
        assert_eq!(
            try_hash_to_curve::<G1Affine, 48>("Aleo BLS12-377 G1"),
            Some((g1, "Aleo BLS12-377 G1 in 1".to_string(), 1))
        );

        // String representation
        assert_eq!(
            g1.x.to_string(),
            "86955166202209252054841725299383634216024564922031151910432342080742656630073360177791133884242980915151545533873",
        );
        assert_eq!(
            g1.y.to_string(),
            "5357432777803398316985742892376180784287827784847282115768792720181668695291733758991500901931533410850796471984",
        );

        // Montgomery BigInteger representation
        assert_eq!(
            g1.x.to_repr(),
            BigInteger384::new([
                9784669934674216369,
                9564223404532400085,
                419570389147391279,
                12135946296701894711,
                15657423922605265599,
                40709594552721325
            ])
        );
        assert_eq!(
            g1.y.to_repr(),
            BigInteger384::new([
                16717527748815095472,
                12751553298161443793,
                18080951552365064848,
                8216371852504494188,
                3630542396628179757,
                2508176635769511
            ])
        );

        // Raw BigInteger representation
        assert_eq!(
            g1.x.to_repr_unchecked(),
            BigInteger384::new([
                12023667888327976710,
                11233871288118439574,
                14774526705544047764,
                11566377490771078655,
                17293331906657813399,
                61120880581657516
            ])
        );
        assert_eq!(
            g1.y.to_repr_unchecked(),
            BigInteger384::new([
                5111409614751470114,
                4786250522143032143,
                10782753916197954560,
                7970186620432000511,
                9400544975888553916,
                22957825900384734
            ])
        );
    }

    #[test]
    fn hash_bls12_377_g2() {
        let g2 = hash_to_curve::<G2Affine, 96>("Aleo BLS12-377 G2 in 3").unwrap();
        assert!(g2.is_on_curve());
        assert!(g2.is_in_correct_subgroup_assuming_on_curve());
        assert_eq!(G2Affine::SERIALIZED_SIZE, 2 * 384 / 8);
        assert_eq!(
            try_hash_to_curve::<G2Affine, 96>("Aleo BLS12-377 G2"),
            Some((g2, "Aleo BLS12-377 G2 in 3".to_string(), 3)),
        );

        // String representation
        assert_eq!(
            g2.x.to_string(),
            "Fp2(114302662622654283009262358063160094701861582474466246461615450026008627444168110612821174822847374597554138837736 + 177274492545224713145929754501896297323234812782955496673928274295405325233171369986159627920108686677981565796566 * u)",
        );
        assert_eq!(
            g2.y.to_string(),
            "Fp2(74332226801492097469250236843422197900845093148840025889564383194204142983525466020956549382567150819615871633674 + 120943082536536619052337621382347303140058776161798872583113748881793839821724088417521694169555147388195170408124 * u)",
        );

        // Montgomery BigInteger representation
        assert_eq!(
            g2.x.c0.to_repr(),
            BigInteger384::new([
                1397962934160257768,
                11332849711829726066,
                2385670344731545327,
                9083597898815202729,
                6157796690343434792,
                53512807287884029
            ])
        );
        assert_eq!(
            g2.x.c1.to_repr(),
            BigInteger384::new([
                4361969924092969174,
                9926919709900030531,
                17393823957599063769,
                12718571106725679016,
                4314580779096823239,
                82994180003903692
            ])
        );
        assert_eq!(
            g2.y.c0.to_repr(),
            BigInteger384::new([
                18083856496506734858,
                4435983470393956653,
                953048484679161560,
                8073133679361616483,
                14177086701956890706,
                34799942860816324
            ])
        );
        assert_eq!(
            g2.y.c1.to_repr(),
            BigInteger384::new([
                9748019184513832636,
                8505354102433525464,
                6110438564624788823,
                12651190201403001841,
                18235155128668310818,
                56621636977489042
            ])
        );

        // Raw BigInteger representation
        assert_eq!(
            g2.x.c0.to_repr_unchecked(),
            BigInteger384::new([
                856482368279856668,
                5793074389089131118,
                4596676208872117598,
                9025112746984268665,
                16328227140964044855,
                44781449420474798
            ])
        );
        assert_eq!(
            g2.x.c1.to_repr_unchecked(),
            BigInteger384::new([
                12346803832623055560,
                4786264628284220908,
                6689501809078044958,
                675907838195598545,
                14712648858795088551,
                96143144554192752
            ])
        );
        assert_eq!(
            g2.y.c0.to_repr_unchecked(),
            BigInteger384::new([
                7564421354282524249,
                11235739172967913084,
                721984723544260566,
                75889195665323699,
                11493645154932710602,
                12743107328700345
            ])
        );
        assert_eq!(
            g2.y.c1.to_repr_unchecked(),
            BigInteger384::new([
                12086936954681951615,
                4444366098968706288,
                2347403901584830576,
                17264363775481626969,
                6042419194053018638,
                76454474019252244
            ])
        );
    }
}

#[cfg(test)]
mod bw6_761 {
    use crate::hash_to_curve::{hash_to_curve, try_hash_to_curve};
    use snarkvm_curves::{
        bw6_761::{G1Affine, G2Affine},
        AffineCurve,
    };
    use snarkvm_fields::PrimeField;
    use snarkvm_utilities::{BigInteger768, ConstantSerializedSize};

    #[test]
    fn hash_bw6_761_g1() {
        let g1 = hash_to_curve::<G1Affine, 96>("Aleo BW6-761 G1 in 2").unwrap();
        assert!(g1.is_on_curve());
        assert!(g1.is_in_correct_subgroup_assuming_on_curve());
        assert_eq!(G1Affine::SERIALIZED_SIZE, 768 / 8);
        assert_eq!(
            try_hash_to_curve::<G1Affine, 96>("Aleo BW6-761 G1"),
            Some((g1, "Aleo BW6-761 G1 in 2".to_string(), 2)),
        );

        // String representation
        assert_eq!(
            g1.x.to_string(),
            "3084896818094878465292814035026544910974143312995562714531210009417331019378722146056734617855323490417282419020353456806408059861474535810136628528514505922764873548629590004235442353333669842235683054328901866065961461891480718",
        );
        assert_eq!(
            g1.y.to_string(),
            "1722594430950431707034270778095718452934841892751405378948646210663260689333231099444985491480265568831760089926199287574304741119620587413810767542016852955943987284555845710626492919005786351909684459798008230268853750112996119",
        );

        // Montgomery BigInteger representation
        assert_eq!(
            g1.x.to_repr(),
            BigInteger768::new([
                2537311460008148110,
                14641026675997586748,
                15681397883737574864,
                3515734269088683239,
                10667520927575987125,
                12913462782050895385,
                11704664247061851537,
                1468129860379459429,
                16310423809131021494,
                4013821542321333091,
                4445006454017963416,
                36654195773568420
            ]),
        );
        assert_eq!(
            g1.y.to_repr(),
            BigInteger768::new([
                14014611516177533719,
                17903016839392992451,
                9196200350355285889,
                6683114763538366914,
                5150712113333547561,
                8943397975547316395,
                2004575478557712559,
                2032859064883600230,
                12439052051264647521,
                15936436815807570052,
                8131464412416887335,
                20467560905167973
            ]),
        );

        // Raw BigInteger representation
        assert_eq!(
            g1.x.to_repr_unchecked(),
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
            ]),
        );
        assert_eq!(
            g1.y.to_repr_unchecked(),
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
            ]),
        );
    }

    #[test]
    fn hash_bw6_761_g2() {
        let g2 = hash_to_curve::<G2Affine, 96>("Aleo BW6-761 G2 in 1").unwrap();
        assert!(g2.is_on_curve());
        assert!(g2.is_in_correct_subgroup_assuming_on_curve());
        assert_eq!(G2Affine::SERIALIZED_SIZE, 768 / 8);
        assert_eq!(
            try_hash_to_curve::<G2Affine, 96>("Aleo BW6-761 G2"),
            Some((g2, "Aleo BW6-761 G2 in 1".to_string(), 1)),
        );

        // String representation
        assert_eq!(
            g2.x.to_string(),
            "1379824447046925053925803516826446813666959713660132146475377855840887530465700664266093320822990396082877604866921473089513727526853937217821005026837326271717122092248464798535668290526656694215408161034640476309747843577646970",
        );
        assert_eq!(
            g2.y.to_string(),
            "1050835022300138814583100651620759903348576607200595979410703998840829490733434315904240321139330355343841234020929419484656826745390468123520124426608430511537222419205835734084682075320421490148265889052675642775233610569345393",
        );

        // Montgomery BigInteger representation
        assert_eq!(
            g2.x.to_repr(),
            BigInteger768::new([
                10752252536851500922,
                6481572160793730753,
                13281794307222049949,
                10481751510777910837,
                4537456867202203772,
                15637965193048613578,
                5713835461892635065,
                4084317906254198675,
                16943331595061180137,
                9577357605014723349,
                5363920379136608601,
                16394828870304947
            ]),
        );
        assert_eq!(
            g2.y.to_repr(),
            BigInteger768::new([
                7180145502708951409,
                5138236133464296180,
                1247844464283606958,
                2283651051810112894,
                18434773500867497040,
                9199124881016633715,
                7168084859093512082,
                13403784119011182058,
                11861190494300040826,
                11703909866938065101,
                11616691420705964960,
                12485834990389875
            ]),
        );

        // Raw BigInteger representation
        assert_eq!(
            g2.x.to_repr_unchecked(),
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
            ]),
        );
        assert_eq!(
            g2.y.to_repr_unchecked(),
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
            ]),
        );
    }
}
