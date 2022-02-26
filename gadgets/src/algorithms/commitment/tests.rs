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
use snarkvm_algorithms::{commitment::BHPCommitment, CommitmentScheme};
use snarkvm_curves::edwards_bls12::{EdwardsProjective, Fq};
use snarkvm_r1cs::{ConstraintSystem, TestConstraintSystem};
use snarkvm_utilities::rand::{test_rng, UniformRand};

use rand::Rng;
use rand_xorshift::XorShiftRng;

const ITERATIONS: usize = 1000;

fn native_and_gadget_equivalence_test<Native: CommitmentScheme, Gadget: CommitmentGadget<Native, Fq>>(
    rng: &mut XorShiftRng,
) -> (<Native as CommitmentScheme>::Output, <Gadget as CommitmentGadget<Native, Fq>>::OutputGadget) {
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
    let commitment_gadget =
        Gadget::alloc_constant(&mut cs.ns(|| "parameters_gadget"), || Ok(&commitment_scheme)).unwrap();
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

    let mut rng = test_rng();

    for _ in 0..ITERATIONS {
        let (native_output, gadget_output) =
            native_and_gadget_equivalence_test::<TestCommitment, TestCommitmentGadget>(&mut rng);
        assert_eq!(native_output, gadget_output.get_value().unwrap());
    }
}

#[cfg(test)]
mod value_balance_commitment_gadget_tests {
    use crate::{
        algorithms::commitment::ValueBalanceCommitmentVerificationGadget,
        boolean::Boolean,
        curves::edwards_bls12::EdwardsBls12Gadget,
        traits::{alloc::AllocGadget, ValueBalanceCommitmentGadget},
        uint::UInt8,
    };

    use snarkvm_algorithms::{
        commitment::{value_balance::*, PedersenCompressedCommitment},
        errors::ValueBalanceCommitmentError,
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
    type VerificationGadget = ValueBalanceCommitmentVerificationGadget<G, Fr, EdwardsBls12Gadget>;

    fn generate_random_value_balance_commitment<C: CommitmentScheme, R: Rng>(
        value_commitment: &C,
        input_amounts: Vec<u64>,
        output_amounts: Vec<u64>,
        sighash: &[u8],
        rng: &mut R,
    ) -> Result<(Vec<C::Output>, Vec<C::Output>, i64, ValueBalanceCommitment), ValueBalanceCommitmentError> {
        let mut value_balance: i64 = 0;

        let mut input_value_commitment_randomness = vec![];
        let mut input_value_commitments = vec![];

        let mut output_value_commitment_randomness = vec![];
        let mut output_value_commitments = vec![];

        for input_amount in input_amounts {
            value_balance += input_amount as i64;

            let value_commit_randomness = C::Randomness::rand(rng);
            let value_commitment =
                value_commitment.commit(&input_amount.to_le_bytes(), &value_commit_randomness).unwrap();

            input_value_commitment_randomness.push(value_commit_randomness);
            input_value_commitments.push(value_commitment);
        }

        for output_amount in output_amounts {
            value_balance -= output_amount as i64;

            let value_commit_randomness = C::Randomness::rand(rng);
            let value_commitment =
                value_commitment.commit(&output_amount.to_le_bytes(), &value_commit_randomness).unwrap();

            output_value_commitment_randomness.push(value_commit_randomness);
            output_value_commitments.push(value_commitment);
        }

        let value_balance_commitment = commit_value_balance::<_, G, _>(
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

        Ok((input_value_commitments, output_value_commitments, value_balance, value_balance_commitment))
    }

    #[test]
    fn test_value_balance_commitment_gadget() {
        let rng = &mut rand::thread_rng();
        let mut cs = TestConstraintSystem::<Fr>::new();

        // Setup parameters

        let value_commitment = ValueCommitment::setup("value_balance_commitment_test");

        let input_amount: u64 = rng.gen_range(0..100000000);
        let input_amount_2: u64 = rng.gen_range(0..100000000);
        let output_amount: u64 = rng.gen_range(0..100000000);
        let output_amount_2: u64 = rng.gen_range(0..100000000);

        let sighash = [1u8; 64].to_vec();

        let (input_value_commitments, output_value_commitments, value_balance, value_balance_commitment) =
            generate_random_value_balance_commitment::<ValueCommitment, _>(
                &value_commitment,
                vec![input_amount, input_amount_2],
                vec![output_amount, output_amount_2],
                &sighash,
                rng,
            )
            .unwrap();

        // Verify the value balance commitment

        let verified = verify_value_balance_commitment::<ValueCommitment, G>(
            &value_commitment,
            &input_value_commitments,
            &output_value_commitments,
            value_balance,
            &sighash,
            &value_balance_commitment,
        )
        .unwrap();

        assert!(verified);

        let (c, partial_bvk, affine_r, recommit) = gadget_verification_setup::<ValueCommitment, G>(
            &value_commitment,
            &input_value_commitments,
            &output_value_commitments,
            &sighash,
            &value_balance_commitment,
        )
        .unwrap();

        // Allocate gadget values
        let commitment_scheme_gadget =
            <VerificationGadget as ValueBalanceCommitmentGadget<ValueCommitment, _, _>>::CommitmentGadget::alloc_constant(
                &mut cs.ns(|| "commitment_scheme_gadget"),
                || Ok(value_commitment),
            )
                .unwrap();

        let c_gadget =
            <VerificationGadget as ValueBalanceCommitmentGadget<ValueCommitment, _, _>>::RandomnessGadget::alloc(
                &mut cs.ns(|| "c_gadget"),
                || Ok(&c),
            )
            .unwrap();

        let partial_bvk_gadget =
            <VerificationGadget as ValueBalanceCommitmentGadget<ValueCommitment, _, _>>::OutputGadget::alloc(
                &mut cs.ns(|| "partial_bvk_gadget"),
                || Ok(partial_bvk),
            )
            .unwrap();

        let affine_r_gadget =
            <VerificationGadget as ValueBalanceCommitmentGadget<ValueCommitment, _, _>>::OutputGadget::alloc(
                &mut cs.ns(|| "affine_r_gadget"),
                || Ok(affine_r),
            )
            .unwrap();

        let recommit_gadget =
            <VerificationGadget as ValueBalanceCommitmentGadget<ValueCommitment, _, _>>::OutputGadget::alloc(
                &mut cs.ns(|| "recommit_gadget"),
                || Ok(recommit),
            )
            .unwrap();

        let value_balance_bytes =
            UInt8::alloc_vec(cs.ns(|| "value_balance_bytes"), &(value_balance.abs() as u64).to_le_bytes()).unwrap();

        let is_negative =
            Boolean::alloc(&mut cs.ns(|| "value_balance_is_negative"), || Ok(value_balance.is_negative())).unwrap();

        let value_balance_comm =
            <VerificationGadget as ValueBalanceCommitmentGadget<ValueCommitment, _, G>>::check_value_commitment_gadget(
                &mut cs.ns(|| "value_balance_commitment"),
                &commitment_scheme_gadget,
                &value_balance_bytes,
            )
            .unwrap();

        <VerificationGadget as ValueBalanceCommitmentGadget<ValueCommitment, _, G>>::check_value_balance_commitment_gadget(
            &mut cs.ns(|| "verify_value_balance_commitment"),
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
}
