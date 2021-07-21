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

use super::*;
use crate::{
    curves::edwards_bls12::EdwardsBls12Gadget,
    integers::uint::UInt8,
    traits::{algorithms::CommitmentGadget, alloc::AllocGadget, FieldGadget},
};
use snarkvm_algorithms::{
    commitment::{
        BHPCommitment,
        BHPCompressedCommitment,
        Blake2sCommitment,
        PedersenCommitment,
        PedersenCompressedCommitment,
    },
    CommitmentScheme,
};
use snarkvm_curves::edwards_bls12::{EdwardsProjective, Fq, Fr};
use snarkvm_r1cs::{ConstraintSystem, TestConstraintSystem};
use snarkvm_utilities::rand::UniformRand;

use rand::{thread_rng, Rng};

const ITERATIONS: usize = 1000;

fn native_and_gadget_equivalence_test<Native: CommitmentScheme, Gadget: CommitmentGadget<Native, Fq>>() -> (
    <Native as CommitmentScheme>::Output,
    <Gadget as CommitmentGadget<Native, Fq>>::OutputGadget,
) {
    let rng = &mut thread_rng();

    // Generate the input message and randomness.
    let input: [u8; 32] = rng.gen();
    let randomness = <Native as CommitmentScheme>::Randomness::rand(rng);

    // Compute the native commitment.
    let commitment_scheme = Native::setup("commitment_test");
    let native_output = commitment_scheme.commit(&input, &randomness).unwrap();

    // Compute the gadget commitment.
    let mut cs = TestConstraintSystem::<Fq>::new();
    let mut input_bytes = vec![];
    for (byte_i, input_byte) in input.iter().enumerate() {
        let cs = cs.ns(|| format!("input_byte_gadget_{}", byte_i));
        input_bytes.push(UInt8::alloc(cs, || Ok(*input_byte)).unwrap());
    }
    let randomness_gadget =
        <Gadget as CommitmentGadget<Native, Fq>>::RandomnessGadget::alloc(&mut cs.ns(|| "randomness_gadget"), || {
            Ok(&randomness)
        })
        .unwrap();
    let commitment_gadget = Gadget::alloc(&mut cs.ns(|| "parameters_gadget"), || Ok(&commitment_scheme)).unwrap();
    let gadget_output = commitment_gadget
        .check_commitment_gadget(&mut cs.ns(|| "commitment_gadget"), &input_bytes, &randomness_gadget)
        .unwrap();
    assert!(cs.is_satisfied());

    (native_output, gadget_output)
}

#[test]
fn bhp_commitment_gadget_test() {
    type TestCommitment = BHPCommitment<EdwardsProjective, 32, 48>;
    type TestCommitmentGadget = BHPCommitmentGadget<EdwardsProjective, Fq, EdwardsBls12Gadget, 32, 48>;

    for _ in 0..ITERATIONS {
        let (native_output, gadget_output) =
            native_and_gadget_equivalence_test::<TestCommitment, TestCommitmentGadget>();
        assert_eq!(native_output.x, gadget_output.x.get_value().unwrap());
        assert_eq!(native_output.y, gadget_output.y.get_value().unwrap());
    }
}

#[test]
fn bhp_compressed_commitment_gadget_test() {
    type TestCommitment = BHPCompressedCommitment<EdwardsProjective, 32, 48>;
    type TestCommitmentGadget = BHPCompressedCommitmentGadget<EdwardsProjective, Fq, EdwardsBls12Gadget, 32, 48>;

    for _ in 0..ITERATIONS {
        let (native_output, gadget_output) =
            native_and_gadget_equivalence_test::<TestCommitment, TestCommitmentGadget>();
        assert_eq!(native_output, gadget_output.get_value().unwrap());
    }
}

#[test]
fn pedersen_commitment_gadget_test() {
    type TestCommitment = PedersenCommitment<EdwardsProjective, 8, 32>;
    type TestCommitmentGadget = PedersenCommitmentGadget<EdwardsProjective, Fq, EdwardsBls12Gadget, 8, 32>;

    for _ in 0..ITERATIONS {
        let (native_output, gadget_output) =
            native_and_gadget_equivalence_test::<TestCommitment, TestCommitmentGadget>();
        assert_eq!(native_output.x, gadget_output.x.get_value().unwrap());
        assert_eq!(native_output.y, gadget_output.y.get_value().unwrap());
    }
}

#[test]
fn pedersen_compressed_commitment_gadget_test() {
    type TestCommitment = PedersenCompressedCommitment<EdwardsProjective, 8, 32>;
    type TestCommitmentGadget = PedersenCompressedCommitmentGadget<EdwardsProjective, Fq, EdwardsBls12Gadget, 8, 32>;

    for _ in 0..ITERATIONS {
        let (native_output, gadget_output) =
            native_and_gadget_equivalence_test::<TestCommitment, TestCommitmentGadget>();
        assert_eq!(native_output, gadget_output.get_value().unwrap());
    }
}

#[test]
fn blake2s_commitment_gadget_test() {
    let mut cs = TestConstraintSystem::<Fr>::new();
    let rng = &mut thread_rng();

    let input: [u8; 32] = rng.gen();

    let mut randomness = [0u8; 32];
    rng.fill(&mut randomness);

    let commitment = Blake2sCommitment::setup("blake2s_commitment_gadget_test");
    let native_result = commitment.commit(&input, &randomness).unwrap();

    let mut input_bytes = vec![];
    for (byte_i, input_byte) in input.iter().enumerate() {
        let cs = cs.ns(|| format!("input_byte_gadget_{}", byte_i));
        input_bytes.push(UInt8::alloc(cs, || Ok(*input_byte)).unwrap());
    }

    let mut randomness_bytes = vec![];
    for (byte_i, random_byte) in randomness.iter().enumerate() {
        let cs = cs.ns(|| format!("randomness_byte_gadget_{}", byte_i));
        randomness_bytes.push(UInt8::alloc(cs, || Ok(*random_byte)).unwrap());
    }
    let randomness_bytes = Blake2sRandomnessGadget(randomness_bytes);

    let blake2s_gadget =
        Blake2sCommitmentGadget::alloc(&mut cs.ns(|| "gadget_parameters"), || Ok(&commitment)).unwrap();
    let gadget_result = blake2s_gadget
        .check_commitment_gadget(&mut cs.ns(|| "gadget_evaluation"), &input_bytes, &randomness_bytes)
        .unwrap();

    for (i, nr) in native_result.iter().enumerate() {
        assert_eq!(*nr, gadget_result.0[i].value.unwrap());
    }
    assert!(cs.is_satisfied());
}
