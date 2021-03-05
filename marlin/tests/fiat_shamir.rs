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

// use ark_mnt4_298::{Fq, Fr};

use snarkvm_curves::bls12_377::{Fq, Fr};
use snarkvm_fields::PrimeField;
use snarkvm_gadgets::utilities::{alloc::AllocGadget, uint::UInt8};
use snarkvm_marlin::fiat_shamir::{
    constraints::{FiatShamirAlgebraicSpongeRngVar, FiatShamirRngVar},
    poseidon::{constraints::PoseidonSpongeVar, PoseidonSponge},
    FiatShamirAlgebraicSpongeRng,
    FiatShamirChaChaRng,
    FiatShamirRng,
};
use snarkvm_nonnative::{params::OptimizationType, NonNativeFieldVar};
use snarkvm_r1cs::{ConstraintSystem, TestConstraintSystem};
use snarkvm_utilities::UniformRand;

use blake2::Blake2s;
use rand::SeedableRng;

const NUM_ABSORBED_RAND_FIELD_ELEMS: usize = 10;
const NUM_ABSORBED_RAND_BYTE_ELEMS: usize = 10;
const SIZE_ABSORBED_BYTE_ELEM: usize = 64;

const NUM_SQUEEZED_FIELD_ELEMS: usize = 10;
const NUM_SQUEEZED_SHORT_FIELD_ELEMS: usize = 10;

#[test]
fn test_chacharng() {
    let rng = &mut rand_chacha::ChaChaRng::seed_from_u64(123456789u64);

    let mut absorbed_rand_field_elems = Vec::new();
    for _ in 0..NUM_ABSORBED_RAND_FIELD_ELEMS {
        absorbed_rand_field_elems.push(Fr::rand(rng));
    }

    let mut absorbed_rand_byte_elems = Vec::<Vec<u8>>::new();
    for _ in 0..NUM_ABSORBED_RAND_BYTE_ELEMS {
        absorbed_rand_byte_elems.push((0..SIZE_ABSORBED_BYTE_ELEM).map(|_| u8::rand(rng)).collect());
    }

    let mut fs_rng = FiatShamirChaChaRng::<Fr, Fq, Blake2s>::new();
    fs_rng.absorb_nonnative_field_elements(&absorbed_rand_field_elems, OptimizationType::Weight);
    for absorbed_rand_byte_elem in absorbed_rand_byte_elems {
        fs_rng.absorb_bytes(&absorbed_rand_byte_elem);
    }

    let _squeezed_fields_elems =
        fs_rng.squeeze_nonnative_field_elements(NUM_SQUEEZED_FIELD_ELEMS, OptimizationType::Weight);
    let _squeezed_short_fields_elems = fs_rng.squeeze_128_bits_nonnative_field_elements(NUM_SQUEEZED_SHORT_FIELD_ELEMS);
}

#[test]
fn test_poseidon() {
    let rng = &mut rand_chacha::ChaChaRng::seed_from_u64(123456789u64);

    let mut absorbed_rand_field_elems = Vec::new();
    for _ in 0..NUM_ABSORBED_RAND_FIELD_ELEMS {
        absorbed_rand_field_elems.push(Fr::rand(rng));
    }

    let mut absorbed_rand_byte_elems = Vec::<Vec<u8>>::new();
    for _ in 0..NUM_ABSORBED_RAND_BYTE_ELEMS {
        absorbed_rand_byte_elems.push((0..SIZE_ABSORBED_BYTE_ELEM).map(|_| u8::rand(rng)).collect());
    }

    // fs_rng in the plaintext world
    let mut fs_rng = FiatShamirAlgebraicSpongeRng::<Fr, Fq, PoseidonSponge<Fq>>::new();

    fs_rng.absorb_nonnative_field_elements(&absorbed_rand_field_elems, OptimizationType::Constraints);

    for absorbed_rand_byte_elem in &absorbed_rand_byte_elems {
        fs_rng.absorb_bytes(absorbed_rand_byte_elem);
    }

    let squeezed_fields_elems =
        fs_rng.squeeze_nonnative_field_elements(NUM_SQUEEZED_FIELD_ELEMS, OptimizationType::Constraints);
    let squeezed_short_fields_elems = fs_rng.squeeze_128_bits_nonnative_field_elements(NUM_SQUEEZED_SHORT_FIELD_ELEMS);

    // fs_rng in the constraint world
    let mut cs = TestConstraintSystem::<Fq>::new();
    // let cs_sys = ConstraintSystem::<Fq>::new();
    // let cs = ConstraintSystemRef::new(cs_sys);
    // cs.set_optimization_goal(OptimizationGoal::Weight);

    let mut fs_rng_gadget =
        FiatShamirAlgebraicSpongeRngVar::<Fr, Fq, PoseidonSponge<Fq>, PoseidonSpongeVar<Fq>>::new(cs.ns(|| "new"));

    let mut absorbed_rand_field_elems_gadgets = Vec::new();
    for (i, absorbed_rand_field_elem) in absorbed_rand_field_elems.iter().enumerate() {
        absorbed_rand_field_elems_gadgets.push(
            NonNativeFieldVar::<Fr, Fq>::alloc_constant(cs.ns(|| format!("alloc_elem_{}", i)), || {
                Ok(absorbed_rand_field_elem)
            })
            .unwrap(),
        );
    }
    fs_rng_gadget
        .absorb_nonnative_field_elements(
            cs.ns(|| "absorb_nonnative_field_elements"),
            &absorbed_rand_field_elems_gadgets,
            OptimizationType::Constraints,
        )
        .unwrap();

    let mut absorbed_rand_byte_elems_gadgets = Vec::<Vec<UInt8>>::new();
    for (i, absorbed_rand_byte_elem) in absorbed_rand_byte_elems.iter().enumerate() {
        let mut byte_gadget = Vec::<UInt8>::new();
        for (j, byte) in absorbed_rand_byte_elem.iter().enumerate() {
            byte_gadget.push(UInt8::alloc(cs.ns(|| format!("alloc_byte_{}_{}", i, j)), || Ok(byte)).unwrap());
        }
        absorbed_rand_byte_elems_gadgets.push(byte_gadget);
    }
    for (i, absorbed_rand_byte_elems_gadget) in absorbed_rand_byte_elems_gadgets.iter().enumerate() {
        fs_rng_gadget
            .absorb_bytes(cs.ns(|| format!("absorb_bytes{}", i)), absorbed_rand_byte_elems_gadget)
            .unwrap();
    }

    let squeezed_fields_elems_gadgets = fs_rng_gadget
        .squeeze_field_elements(cs.ns(|| "squeeze_field_elements"), NUM_SQUEEZED_FIELD_ELEMS)
        .unwrap();

    let squeezed_short_fields_elems_gadgets = fs_rng_gadget
        .squeeze_128_bits_field_elements(
            cs.ns(|| "squeeze_128_bits_field_elements"),
            NUM_SQUEEZED_SHORT_FIELD_ELEMS,
        )
        .unwrap();

    // compare elems
    for (i, (left, right)) in squeezed_fields_elems
        .iter()
        .zip(squeezed_fields_elems_gadgets.iter())
        .enumerate()
    {
        assert_eq!(
            left.into_repr(),
            right.value().unwrap().into_repr(),
            "{}: left = {:?}, right = {:?}",
            i,
            left.into_repr(),
            right.value().unwrap().into_repr()
        );
    }

    // compare short elems
    for (i, (left, right)) in squeezed_short_fields_elems
        .iter()
        .zip(squeezed_short_fields_elems_gadgets.iter())
        .enumerate()
    {
        assert_eq!(
            left.into_repr(),
            right.value().unwrap().into_repr(),
            "{}: left = {:?}, right = {:?}",
            i,
            left.into_repr(),
            right.value().unwrap().into_repr()
        );
    }

    if !cs.is_satisfied() {
        println!("\n=========================================================");
        println!("\nUnsatisfied constraints:");
        println!("\n{:?}", cs.which_is_unsatisfied().unwrap());
        println!("\n=========================================================");
    }
    assert!(cs.is_satisfied());
}
