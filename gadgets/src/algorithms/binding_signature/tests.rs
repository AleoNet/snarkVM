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

use crate::{
    algorithms::binding_signature::BindingSignatureVerificationGadget,
    boolean::Boolean,
    curves::edwards_bls12::EdwardsBls12Gadget,
    traits::{alloc::AllocGadget, BindingSignatureGadget},
    uint::UInt8,
};

use snarkvm_algorithms::{
    binding_signature::*,
    commitment::PedersenCompressedCommitment,
    errors::BindingSignatureError,
    traits::CommitmentScheme,
};
use snarkvm_curves::edwards_bls12::EdwardsProjective;
use snarkvm_r1cs::{ConstraintSystem, Fr, TestConstraintSystem};
use snarkvm_utilities::rand::UniformRand;

use rand::Rng;

type G = EdwardsProjective;

const NUM_WINDOWS: usize = 4;
const WINDOW_SIZE: usize = 350;

type ValueCommitment = PedersenCompressedCommitment<G, NUM_WINDOWS, WINDOW_SIZE>;
type VerificationGadget = BindingSignatureVerificationGadget<G, Fr, EdwardsBls12Gadget>;

fn generate_random_binding_signature<C: CommitmentScheme, R: Rng>(
    value_commitment: &C,
    input_amounts: Vec<u64>,
    output_amounts: Vec<u64>,
    sighash: &Vec<u8>,
    rng: &mut R,
) -> Result<(Vec<C::Output>, Vec<C::Output>, i64, BindingSignature), BindingSignatureError> {
    let mut value_balance: i64 = 0;

    let mut input_value_commitment_randomness = vec![];
    let mut input_value_commitments = vec![];

    let mut output_value_commitment_randomness = vec![];
    let mut output_value_commitments = vec![];

    for input_amount in input_amounts {
        value_balance += input_amount as i64;

        let value_commit_randomness = C::Randomness::rand(rng);
        let value_commitment = value_commitment.commit(&input_amount.to_le_bytes(), &value_commit_randomness).unwrap();

        input_value_commitment_randomness.push(value_commit_randomness);
        input_value_commitments.push(value_commitment);
    }

    for output_amount in output_amounts {
        value_balance -= output_amount as i64;

        let value_commit_randomness = C::Randomness::rand(rng);
        let value_commitment = value_commitment.commit(&output_amount.to_le_bytes(), &value_commit_randomness).unwrap();

        output_value_commitment_randomness.push(value_commit_randomness);
        output_value_commitments.push(value_commitment);
    }

    let binding_signature = create_binding_signature::<_, G, _>(
        value_commitment,
        &input_value_commitments,
        &output_value_commitments,
        &input_value_commitment_randomness,
        &output_value_commitment_randomness,
        value_balance,
        sighash,
        rng,
    )
    .unwrap();

    Ok((input_value_commitments, output_value_commitments, value_balance, binding_signature))
}

#[test]
fn test_binding_signature_gadget() {
    let rng = &mut rand::thread_rng();
    let mut cs = TestConstraintSystem::<Fr>::new();

    // Setup parameters

    let value_commitment = ValueCommitment::setup("binding_signature_test");

    let input_amount: u64 = rng.gen_range(0..100000000);
    let input_amount_2: u64 = rng.gen_range(0..100000000);
    let output_amount: u64 = rng.gen_range(0..100000000);
    let output_amount_2: u64 = rng.gen_range(0..100000000);

    let sighash = [1u8; 64].to_vec();

    let (input_value_commitments, output_value_commitments, value_balance, binding_signature) =
        generate_random_binding_signature::<ValueCommitment, _>(
            &value_commitment,
            vec![input_amount, input_amount_2],
            vec![output_amount, output_amount_2],
            &sighash,
            rng,
        )
        .unwrap();

    // Verify the binding signature

    let verified = verify_binding_signature::<ValueCommitment, G>(
        &value_commitment,
        &input_value_commitments,
        &output_value_commitments,
        value_balance,
        &sighash,
        &binding_signature,
    )
    .unwrap();

    assert!(verified);

    let (c, partial_bvk, affine_r, recommit) = gadget_verification_setup::<ValueCommitment, G>(
        &value_commitment,
        &input_value_commitments,
        &output_value_commitments,
        &sighash,
        &binding_signature,
    )
    .unwrap();

    // Allocate gadget values
    let commitment_scheme_gadget =
        <VerificationGadget as BindingSignatureGadget<ValueCommitment, _, _>>::CommitmentGadget::alloc_constant(
            &mut cs.ns(|| "commitment_scheme_gadget"),
            || Ok(value_commitment),
        )
        .unwrap();

    let c_gadget = <VerificationGadget as BindingSignatureGadget<ValueCommitment, _, _>>::RandomnessGadget::alloc(
        &mut cs.ns(|| "c_gadget"),
        || Ok(&c),
    )
    .unwrap();

    let partial_bvk_gadget =
        <VerificationGadget as BindingSignatureGadget<ValueCommitment, _, _>>::OutputGadget::alloc(
            &mut cs.ns(|| "partial_bvk_gadget"),
            || Ok(partial_bvk),
        )
        .unwrap();

    let affine_r_gadget = <VerificationGadget as BindingSignatureGadget<ValueCommitment, _, _>>::OutputGadget::alloc(
        &mut cs.ns(|| "affine_r_gadget"),
        || Ok(affine_r),
    )
    .unwrap();

    let recommit_gadget = <VerificationGadget as BindingSignatureGadget<ValueCommitment, _, _>>::OutputGadget::alloc(
        &mut cs.ns(|| "recommit_gadget"),
        || Ok(recommit),
    )
    .unwrap();

    let value_balance_bytes =
        UInt8::alloc_vec(cs.ns(|| "value_balance_bytes"), &(value_balance.abs() as u64).to_le_bytes()).unwrap();

    let is_negative =
        Boolean::alloc(&mut cs.ns(|| "value_balance_is_negative"), || Ok(value_balance.is_negative())).unwrap();

    let value_balance_comm =
        <VerificationGadget as BindingSignatureGadget<ValueCommitment, _, G>>::check_value_balance_commitment_gadget(
            &mut cs.ns(|| "value_balance_commitment"),
            &commitment_scheme_gadget,
            &value_balance_bytes,
        )
        .unwrap();

    <VerificationGadget as BindingSignatureGadget<ValueCommitment, _, G>>::check_binding_signature_gadget(
        &mut cs.ns(|| "verify_binding_signature"),
        &partial_bvk_gadget,
        &value_balance_comm,
        &is_negative,
        &c_gadget,
        &affine_r_gadget,
        &recommit_gadget,
    )
    .unwrap();

    if !cs.is_satisfied() {
        println!("which is unsatisfied: {:?}", cs.which_is_unsatisfied().unwrap());
    }
    assert!(cs.is_satisfied());
}
