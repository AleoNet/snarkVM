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

use rand::{thread_rng, Rng, SeedableRng};
use rand_xorshift::XorShiftRng;

use snarkvm_algorithms::{
    crh::{BoweHopwoodPedersenCRH, BoweHopwoodPedersenCompressedCRH, PedersenCRH, PedersenCompressedCRH, PedersenSize},
    traits::{CRHParameters, CRH},
};
use snarkvm_curves::{
    bls12_377::Fr,
    edwards_bls12::{EdwardsAffine, EdwardsProjective},
};
use snarkvm_fields::{Field, PrimeField};
use snarkvm_r1cs::{ConstraintSystem, TestConstraintSystem};

use crate::{
    algorithms::crh::{
        BoweHopwoodPedersenCRHGadget,
        BoweHopwoodPedersenCompressedCRHGadget,
        PedersenCRHGadget,
        PedersenCompressedCRHGadget,
    },
    curves::edwards_bls12::EdwardsBlsGadget,
    integers::uint::UInt8,
    traits::{
        algorithms::{CRHGadget, MaskedCRHGadget},
        alloc::AllocGadget,
        eq::EqGadget,
    },
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) struct Size;

impl PedersenSize for Size {
    const NUM_WINDOWS: usize = 8;
    const WINDOW_SIZE: usize = 128;
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) struct BoweHopwoodSize;

impl PedersenSize for BoweHopwoodSize {
    const NUM_WINDOWS: usize = 32;
    const WINDOW_SIZE: usize = 48;
}

const PEDERSEN_HASH_CONSTRAINTS: usize = 5632;
const PEDERSEN_HASH_CONSTRAINTS_ON_AFFINE: usize = 6656;
const BOWE_HOPWOOD_HASH_CONSTRAINTS: usize = 3974;

fn generate_input<F: Field, CS: ConstraintSystem<F>, R: Rng>(
    mut cs: CS,
    rng: &mut R,
) -> ([u8; 128], Vec<UInt8>, Vec<UInt8>) {
    let mut input = [1u8; 128];
    rng.fill_bytes(&mut input);
    let mut mask = [1u8; 128];
    rng.fill_bytes(&mut mask);

    let mut input_bytes = vec![];
    let mut mask_bytes = vec![];
    for (byte_i, (input_byte, mask_byte)) in input.iter().zip(mask.iter()).enumerate() {
        let cs_input = cs.ns(|| format!("input_byte_gadget_{}", byte_i));
        input_bytes.push(UInt8::alloc(cs_input, || Ok(*input_byte)).unwrap());
        // The mask will later on be extended to be double the size, so we only need half the bits
        // as the input.
        if byte_i % 2 == 0 {
            let cs_mask = cs.ns(|| format!("mask_byte_gadget_{}", byte_i));
            mask_bytes.push(UInt8::alloc(cs_mask, || Ok(*mask_byte)).unwrap());
        }
    }
    (input, input_bytes, mask_bytes)
}

fn primitive_crh_gadget_test<F: Field, H: CRH, CG: CRHGadget<H, F>>(hash_constraints: usize) {
    let rng = &mut XorShiftRng::seed_from_u64(1231275789u64);
    let mut cs = TestConstraintSystem::<F>::new();

    let (input, input_bytes, _mask_bytes) = generate_input(&mut cs, rng);

    println!("input: {:?}", input);
    assert_eq!(cs.num_constraints(), 1536);

    let crh = H::setup(rng);

    println!("parameters: {:?}", crh.parameters());

    let native_result = crh.hash(&input).unwrap();

    println!("output: {:?}", native_result);

    let parameters_gadget =
        <CG as CRHGadget<_, _>>::ParametersGadget::alloc(&mut cs.ns(|| "gadget_parameters"), || Ok(crh.parameters()))
            .unwrap();
    assert_eq!(cs.num_constraints(), 1536);

    let output_gadget = <CG as CRHGadget<_, _>>::check_evaluation_gadget(
        &mut cs.ns(|| "gadget_evaluation"),
        &parameters_gadget,
        input_bytes,
    )
    .unwrap();
    assert_eq!(cs.num_constraints(), hash_constraints);

    let native_result_gadget =
        <CG as CRHGadget<_, _>>::OutputGadget::alloc(&mut cs.ns(|| "native_result"), || Ok(&native_result)).unwrap();

    output_gadget
        .enforce_equal(
            &mut cs.ns(|| "Check that computed crh matches provided output"),
            &native_result_gadget,
        )
        .unwrap();

    assert!(cs.is_satisfied());
}

fn masked_crh_gadget_test<F: PrimeField, H: CRH, CG: MaskedCRHGadget<H, F>>() {
    let rng = &mut thread_rng();
    let mut cs = TestConstraintSystem::<F>::new();

    let (input, input_bytes, mask_bytes) = generate_input(&mut cs, rng);
    assert_eq!(cs.num_constraints(), 1536);

    let crh = H::setup(rng);
    let mask_parameters = H::Parameters::setup(rng);
    let native_result = crh.hash(&input).unwrap();

    let parameters_gadget =
        <CG as CRHGadget<_, _>>::ParametersGadget::alloc(&mut cs.ns(|| "gadget_parameters"), || Ok(crh.parameters()))
            .unwrap();
    assert_eq!(cs.num_constraints(), 1536);

    let mask_parameters_gadget =
        <CG as CRHGadget<_, _>>::ParametersGadget::alloc(&mut cs.ns(|| "gadget_mask_parameters"), || {
            Ok(mask_parameters)
        })
        .unwrap();
    assert_eq!(cs.num_constraints(), 1536);

    let masked_output_gadget = <CG as MaskedCRHGadget<_, _>>::check_evaluation_gadget_masked(
        &mut cs.ns(|| "masked_gadget_evaluation"),
        &parameters_gadget,
        input_bytes,
        &mask_parameters_gadget,
        mask_bytes,
    )
    .unwrap();
    assert_eq!(cs.num_constraints(), 17932);

    let native_result_gadget =
        <CG as CRHGadget<_, _>>::OutputGadget::alloc(&mut cs.ns(|| "native_result"), || Ok(&native_result)).unwrap();

    masked_output_gadget
        .enforce_equal(
            &mut cs.ns(|| "Check that computed crh matches provided output"),
            &native_result_gadget,
        )
        .unwrap();

    assert!(cs.is_satisfied());
}

mod pedersen_crh_gadget_on_projective {
    use super::*;

    type TestCRH = PedersenCRH<EdwardsProjective, Size>;
    type TestCRHGadget = PedersenCRHGadget<EdwardsProjective, Fr, EdwardsBlsGadget>;

    #[test]
    fn primitive_gadget_test() {
        primitive_crh_gadget_test::<Fr, TestCRH, TestCRHGadget>(PEDERSEN_HASH_CONSTRAINTS)
    }

    #[test]
    fn masked_gadget_test() {
        masked_crh_gadget_test::<Fr, TestCRH, TestCRHGadget>()
    }
}

mod pedersen_crh_gadget_on_affine {
    use super::*;

    type TestCRH = PedersenCRH<EdwardsAffine, Size>;
    type TestCRHGadget = PedersenCRHGadget<EdwardsAffine, Fr, EdwardsBlsGadget>;

    #[test]
    fn primitive_gadget_test() {
        primitive_crh_gadget_test::<Fr, TestCRH, TestCRHGadget>(PEDERSEN_HASH_CONSTRAINTS_ON_AFFINE)
    }
}

mod pedersen_compressed_crh_gadget_on_projective {
    use super::*;

    type TestCRH = PedersenCompressedCRH<EdwardsProjective, Size>;
    type TestCRHGadget = PedersenCompressedCRHGadget<EdwardsProjective, Fr, EdwardsBlsGadget>;

    #[test]
    fn primitive_gadget_test() {
        primitive_crh_gadget_test::<Fr, TestCRH, TestCRHGadget>(PEDERSEN_HASH_CONSTRAINTS)
    }

    #[test]
    fn masked_gadget_test() {
        masked_crh_gadget_test::<Fr, TestCRH, TestCRHGadget>()
    }
}

// Note: Bowe-Hopwood CRH Gadget currently does not support affine curves or masked crh

mod bowe_hopwood_pedersen_crh_gadget_on_projective {
    use super::*;

    type TestCRH = BoweHopwoodPedersenCRH<EdwardsProjective, BoweHopwoodSize>;
    type TestCRHGadget = BoweHopwoodPedersenCRHGadget<EdwardsProjective, Fr, EdwardsBlsGadget>;

    #[test]
    fn primitive_gadget_test() {
        primitive_crh_gadget_test::<Fr, TestCRH, TestCRHGadget>(BOWE_HOPWOOD_HASH_CONSTRAINTS)
    }
}

mod bowe_hopwood_pedersen_compressed_crh_gadget_on_projective {
    use super::*;

    type TestCRH = BoweHopwoodPedersenCompressedCRH<EdwardsProjective, BoweHopwoodSize>;
    type TestCRHGadget = BoweHopwoodPedersenCompressedCRHGadget<EdwardsProjective, Fr, EdwardsBlsGadget>;

    #[test]
    fn primitive_gadget_test() {
        primitive_crh_gadget_test::<Fr, TestCRH, TestCRHGadget>(BOWE_HOPWOOD_HASH_CONSTRAINTS)
    }
}

mod testing_fr_reconstruction {
    use super::*;

    use snarkvm_utilities::BigInteger256;
    use std::str::FromStr;

    type TestCRH = PedersenCRH<EdwardsAffine, Size>;
    type TestCRHGadget = PedersenCRHGadget<EdwardsAffine, Fr, EdwardsBlsGadget>;

    #[test]
    fn test_fr_reconstruction() {
        use snarkvm_utilities::UniformRand;

        let rng = &mut XorShiftRng::seed_from_u64(1231275789u64);

        // Generate a random Fr

        let fr = Fr::rand(rng);

        println!("fr_display: {}", fr); //885547562345160906682910305868884631699585740850634779714003650546253320827
        println!("fr_display: {:?}", fr); //885547562345160906682910305868884631699585740850634779714003650546253320827
        println!("fr_display bigint: {}", fr.0); //55764638695670914121398268152101712757543387694409633574334945402112658761
        println!("fr_debug bigint: {:?}", fr.0); // 07BD286F34D1AD1602F8381D782541284FDB849F7DC97ADE3C28D1E02DA34D49
        println!("fr bigint limbs: {:?}", fr.0.0); // [4334945402112658761, 5754338769440963294, 213982681521013032, 557646386956446998]

        // Attempt to recover Fr from it's display function.
        let fr_display =
            Fr::from_str("885547562345160906682910305868884631699585740850634779714003650546253320827").unwrap();

        println!("");
        println!("fr_display: {}", fr_display); //14107586584977582527300466197919129171679006581820863674418121000810567586427
        println!("fr_display bigint: {}", fr_display.0); //18723113996415202615339078282337681069158823507295401267996291954243879950251
        println!("fr_display bigint debug: {:?}", fr_display.0); // 02992DBAD47068DBD4DF5A6D88A56EAEDC6971D71867C8105751830C7179D7AB
        println!("fr_display bigint limbs: {:?}", fr_display.0.0); // [6291954243879950251, 15882350729540126736, 15339078282337676974, 187231139963889883]

        // Attempt to recover Fr from it's BigInteger display function.
        let fr_bigint =
            Fr::from_str("55764638695644699821398268152101303257543387694409632944334945402112658761").unwrap();

        println!("");
        println!("fr_bigint: {}", fr_bigint); //8883819483587674103088221421147696061809626255954017661115136460566464515401
        println!("fr_bigint bigint: {}", fr_bigint.0); //294868059180736665160756640020363010711361748286514747236817467756854433468162
        println!("fr_bigint bigint debug: {:?}", fr_bigint.0); // 041794F0030FA09ADF183B3CC1E86D10BCFB0484701569B1F269F04F9B66CF02
        println!("fr_bigint bigint limbs: {:?}", fr_bigint.0.0); // [17467756854433468162, 13617482865147472305, 16075664002036296976, 294868059180474522]

        {
            // Attempt to recover Fr from it's BigInteger display function. Just for testing purposes. Leo uses the "from_str" method.
            // This will work.
            let initial_big_int = BigInteger256([
                4334945402112658761,
                5754338769440963294,
                213982681521013032,
                557646386956446998,
            ]);
            let fr_from_repr_raw = Fr::from_repr_raw(initial_big_int); // the `from_repr` function wont work.

            println!("");
            println!("fr_bigint: {}", fr_from_repr_raw); //885547562345160906682910305868884631699585740850634779714003650546253320827
            println!("fr_bigint bigint: {}", fr_from_repr_raw.0); //55764638695670914121398268152101712757543387694409633574334945402112658761
            println!("fr_bigint bigint debug: {:?}", fr_from_repr_raw.0); // 07BD286F34D1AD1602F8381D782541284FDB849F7DC97ADE3C28D1E02DA34D49
            println!("fr_bigint bigint limbs: {:?}", fr_from_repr_raw.0.0); // [4334945402112658761, 5754338769440963294, 213982681521013032, 557646386956446998]

            assert_eq!(fr, fr_from_repr_raw);
        }

        // Confirm that one of the `from_str` impls was valid.
        assert!((fr == fr_display) || (fr == fr_bigint));
    }
}
