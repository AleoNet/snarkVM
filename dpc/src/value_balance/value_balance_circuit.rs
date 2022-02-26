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

use snarkvm_algorithms::{commitment::PedersenCompressedCommitment, CommitmentScheme};
use snarkvm_curves::{Group, ProjectiveCurve};
use snarkvm_fields::{Field, PrimeField};
use snarkvm_gadgets::{
    algorithms::commitment::{pedersen::*, PedersenCompressedCommitmentGadget},
    bits::Boolean,
    integers::uint::UInt8,
    traits::{alloc::AllocGadget, eq::EqGadget, integers::Integer, CommitmentGadget, CompressedGroupGadget},
    ToBytesGadget,
};
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};

use std::{fmt::Debug, marker::PhantomData};

pub trait ValueBalanceCommitmentGadget<C: CommitmentScheme, F: Field, G: Group + ProjectiveCurve> {
    type CommitmentGadget: CommitmentGadget<C, F> + Clone;
    type OutputGadget: EqGadget<F> + ToBytesGadget<F> + AllocGadget<G, F> + Clone + Sized + Debug;
    type RandomnessGadget: AllocGadget<C::Randomness, F> + Clone;

    fn check_value_commitment_gadget<CS: ConstraintSystem<F>>(
        cs: CS,
        commitment_scheme: &Self::CommitmentGadget,
        input: &[UInt8],
    ) -> Result<Self::OutputGadget, SynthesisError>;

    fn check_value_balance_commitment_gadget<CS: ConstraintSystem<F>>(
        cs: CS,
        partial_bvk: &Self::OutputGadget,
        value_balance_comm: &Self::OutputGadget,
        is_negative: &Boolean,
        c: &Self::RandomnessGadget,
        affine_r: &Self::OutputGadget,
        recommit: &Self::OutputGadget,
    ) -> Result<(), SynthesisError>;
}

pub struct ValueBalanceCommitmentVerificationGadget<
    G: Group + ProjectiveCurve,
    F: Field,
    GG: CompressedGroupGadget<G, F>,
>(PhantomData<G>, PhantomData<GG>, PhantomData<F>);

impl<
    F: PrimeField,
    G: Group + ProjectiveCurve,
    GG: CompressedGroupGadget<G, F>,
    const NUM_WINDOWS: usize,
    const WINDOW_SIZE: usize,
> ValueBalanceCommitmentGadget<PedersenCompressedCommitment<G, NUM_WINDOWS, WINDOW_SIZE>, F, G>
    for ValueBalanceCommitmentVerificationGadget<G, F, GG>
{
    type CommitmentGadget = PedersenCompressedCommitmentGadget<G, F, GG, NUM_WINDOWS, WINDOW_SIZE>;
    type OutputGadget = GG;
    type RandomnessGadget = PedersenRandomnessGadget<G>;

    fn check_value_commitment_gadget<CS: ConstraintSystem<F>>(
        mut cs: CS,
        commitment_scheme: &Self::CommitmentGadget,
        input: &[UInt8],
    ) -> Result<Self::OutputGadget, SynthesisError> {
        let default_randomness = Self::RandomnessGadget::alloc(&mut cs.ns(|| "default_randomness"), || {
            Ok(<G as Group>::ScalarField::default())
        })?;

        let output = commitment_scheme.pedersen.check_commitment_gadget(cs, input, &default_randomness)?;
        Ok(output)
    }

    fn check_value_balance_commitment_gadget<CS: ConstraintSystem<F>>(
        mut cs: CS,
        partial_bvk: &Self::OutputGadget,
        value_balance_comm: &Self::OutputGadget,
        is_negative: &Boolean,
        c: &Self::RandomnessGadget,
        affine_r: &Self::OutputGadget,
        recommit: &Self::OutputGadget,
    ) -> Result<(), SynthesisError> {
        // TODO (raychu86) make this circuit more efficient

        let negative_bvk = partial_bvk.add(cs.ns(|| "construct_negative_bvk"), value_balance_comm)?;
        let positive_bvk = partial_bvk.sub(cs.ns(|| "construct_positive_bvk"), value_balance_comm)?;

        let c_bits: Vec<_> = c.0.iter().flat_map(|byte| byte.to_bits_le()).collect();
        let zero = GG::zero(&mut cs.ns(|| "zero")).unwrap();

        let negative_result = negative_bvk.mul_bits(cs.ns(|| "mul_bits_negative"), &zero, c_bits.iter().cloned())?;
        let positive_result = positive_bvk.mul_bits(cs.ns(|| "mul_bits_positive"), &zero, c_bits.iter().cloned())?;

        let temp = affine_r.sub(cs.ns(|| "sub_recommit"), recommit)?;
        let negative_result = negative_result.add(cs.ns(|| "add_temp"), &temp)?;
        let positive_result = positive_result.add(cs.ns(|| "add_temp2"), &temp)?;

        let result = GG::conditionally_select(
            cs.ns(|| "select result"),
            &is_negative.not(),
            &positive_result,
            &negative_result,
        )?;

        result.enforce_equal(&mut cs.ns(|| "Check that the value balance commitment verifies"), &zero)?;

        Ok(())
    }
}

#[cfg(test)]
mod value_balance_commitment_gadget_tests {
    use super::*;
    use crate::testnet2::Testnet2;use crate::Network;
    use crate::value_balance::*;
    use snarkvm_curves::edwards_bls12::EdwardsProjective;
    use snarkvm_gadgets::curves::edwards_bls12::EdwardsBls12Gadget;
    use snarkvm_r1cs::{ConstraintSystem, Fr, TestConstraintSystem};
    use snarkvm_utilities::rand::UniformRand;

    use rand::Rng;

    type G = <Testnet2 as Network>::ProgramProjectiveCurve;
    type ValueCommitment = <Testnet2 as Network>::ValueCommitment;
    type VerificationGadget = ValueBalanceCommitmentVerificationGadget<G, Fr, EdwardsBls12Gadget>;

    #[test]
    fn test_value_balance_commitment_gadget() {
        let rng = &mut rand::thread_rng();
        let mut cs = TestConstraintSystem::<Fr>::new();

        let input_amount: u64 = rng.gen_range(0..100000000);
        let input_amount_2: u64 = rng.gen_range(0..100000000);
        let output_amount: u64 = rng.gen_range(0..100000000);
        let output_amount_2: u64 = rng.gen_range(0..100000000);
        let sighash = [1u8; 64].to_vec();

        let (input_value_commitments, output_value_commitments, value_balance, value_balance_commitment) =
            crate::value_balance::tests::generate_random_value_balance_commitment::<Testnet2, _>(
                vec![input_amount, input_amount_2],
                vec![output_amount, output_amount_2],
                &sighash,
                rng,
            );

        // Verify the value balance commitment.
        assert!(verify_value_balance_commitment::<Testnet2>(
            &input_value_commitments,
            &output_value_commitments,
            value_balance,
            &sighash,
            &value_balance_commitment,
        )
            .unwrap());

        let (c, partial_bvk, affine_r, recommit) = gadget_verification_setup::<Testnet2>(
            &input_value_commitments,
            &output_value_commitments,
            &sighash,
            &value_balance_commitment,
        )
        .unwrap();

        // Allocate gadget values
        let commitment_scheme_gadget =
            <Testnet2 as Network>::ValueCommitmentGadget::alloc_constant(
                &mut cs.ns(|| "commitment_scheme_gadget"),
                || Ok(<Testnet2 as Network>::value_commitment()),
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
