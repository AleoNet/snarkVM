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

use crate::Network;
use snarkvm_fields::Zero;
use snarkvm_gadgets::{
    bits::Boolean,
    integers::uint::UInt8,
    traits::{alloc::AllocGadget, CommitmentGadget},
    CondSelectGadget,
    EqGadget,
    GroupGadget,
    ToBitsLEGadget,
};
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};

use std::marker::PhantomData;

pub struct ValueBalanceCommitmentGadget<N: Network>(PhantomData<N>);

impl<N: Network> ValueBalanceCommitmentGadget<N> {
    /// Returns a commitment on the input with a randomness of zero.
    pub fn check_commitment_without_randomness_gadget<CS: ConstraintSystem<N::InnerScalarField>>(
        mut cs: CS,
        commitment_scheme: &N::ValueCommitmentGadget,
        input: &[UInt8],
    ) -> Result<
        <N::ValueCommitmentGadget as CommitmentGadget<N::ValueCommitmentScheme, N::InnerScalarField>>::OutputGadget,
        SynthesisError,
    > {
        let zero_randomness = <N::ValueCommitmentGadget as CommitmentGadget<_, _>>::RandomnessGadget::alloc(
            &mut cs.ns(|| "zero_randomness"),
            || Ok(N::ProgramScalarField::zero()),
        )?;

        commitment_scheme.check_commitment_gadget(cs, input, &zero_randomness)
    }

    #[rustfmt::skip]
    /// Check that the value balance commitment is valid.
    pub fn check_value_balance_commitment_gadget<CS: ConstraintSystem<N::InnerScalarField>>(
        mut cs: CS,
        partial_combined_commitments: &<N::ValueCommitmentGadget as CommitmentGadget<
            N::ValueCommitmentScheme,
            N::InnerScalarField,
        >>::OutputGadget,
        value_balance_comm: &<N::ValueCommitmentGadget as CommitmentGadget<
            N::ValueCommitmentScheme,
            N::InnerScalarField,
        >>::OutputGadget,
        is_negative: &Boolean,
        c: &<N::ValueCommitmentGadget as CommitmentGadget<N::ValueCommitmentScheme, N::InnerScalarField>>::RandomnessGadget,
        commitment: &<N::ValueCommitmentGadget as CommitmentGadget<N::ValueCommitmentScheme, N::InnerScalarField>>::OutputGadget,
        blinded_commitment: &<N::ValueCommitmentGadget as CommitmentGadget<
            N::ValueCommitmentScheme,
            N::InnerScalarField,
        >>::OutputGadget,
    ) -> Result<(), SynthesisError> {
        // TODO (raychu86) make this circuit more efficient

        let negative_combined_commitments = partial_combined_commitments
            .add(cs.ns(|| "construct_negative_combined_commitments"), value_balance_comm)?;
        let positive_combined_commitments = partial_combined_commitments
            .sub(cs.ns(|| "construct_positive_combined_commitments"), value_balance_comm)?;

        let c_bits: Vec<_> = c.to_bits_le(cs.ns(|| "c.to_bits_le()"))?;
        let zero =
            <N::ValueCommitmentGadget as CommitmentGadget<_, _>>::OutputGadget::zero(&mut cs.ns(|| "zero")).unwrap();

        let negative_result =
            negative_combined_commitments.mul_bits(cs.ns(|| "mul_bits_negative"), &zero, c_bits.iter().cloned())?;
        let positive_result =
            positive_combined_commitments.mul_bits(cs.ns(|| "mul_bits_positive"), &zero, c_bits.iter().cloned())?;

        let temp = commitment.sub(cs.ns(|| "sub_blinded_commitment"), blinded_commitment)?;
        let negative_result = negative_result.add(cs.ns(|| "add_temp"), &temp)?;
        let positive_result = positive_result.add(cs.ns(|| "add_temp2"), &temp)?;

        let result = <N::ValueCommitmentGadget as CommitmentGadget<_, _>>::OutputGadget::conditionally_select(
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
mod tests {
    use super::*;
    use crate::{testnet2::Testnet2, value_balance::*, Network};
    use snarkvm_r1cs::{ConstraintSystem, Fr, TestConstraintSystem};

    use rand::Rng;

    #[test]
    fn test_value_balance_commitment_gadget() {
        let rng = &mut rand::thread_rng();
        let mut cs = TestConstraintSystem::<Fr>::new();

        let input_amount = AleoAmount::from_gate(rng.gen_range(0..100000000));
        let input_amount_2 = AleoAmount::from_gate(rng.gen_range(0..100000000));
        let output_amount = AleoAmount::from_gate(rng.gen_range(0..100000000));
        let output_amount_2 = AleoAmount::from_gate(rng.gen_range(0..100000000));
        let sighash = [1u8; 64].to_vec();

        let (input_value_commitments, output_value_commitments, value_balance, value_balance_commitment) =
            crate::value_balance::tests::generate_random_value_balance_commitment::<Testnet2, _>(
                vec![input_amount, input_amount_2],
                vec![output_amount, output_amount_2],
                &sighash,
                rng,
            );

        // Verify the value balance commitment.
        assert!(
            value_balance_commitment
                .verify(&input_value_commitments, &output_value_commitments, value_balance, &sighash,)
                .unwrap()
        );

        let (c, partial_combined_commitments, zero_commitment, blinded_commitment) = value_balance_commitment
            .gadget_verification_setup(&input_value_commitments, &output_value_commitments, &sighash)
            .unwrap();

        // Allocate gadget values
        let commitment_scheme_gadget = <Testnet2 as Network>::ValueCommitmentGadget::alloc_constant(
            &mut cs.ns(|| "commitment_scheme_gadget"),
            || Ok(<Testnet2 as Network>::value_commitment_scheme()),
        )
        .unwrap();

        let c_gadget =
            <<Testnet2 as Network>::ValueCommitmentGadget as CommitmentGadget<_, _>>::RandomnessGadget::alloc(
                &mut cs.ns(|| "c_gadget"),
                || Ok(&c),
            )
            .unwrap();

        let partial_combined_commitments_gadget =
            <<Testnet2 as Network>::ValueCommitmentGadget as CommitmentGadget<_, _>>::OutputGadget::alloc(
                &mut cs.ns(|| "partial_combined_commitments_gadget"),
                || Ok(partial_combined_commitments),
            )
            .unwrap();

        let zero_commitment_gadget =
            <<Testnet2 as Network>::ValueCommitmentGadget as CommitmentGadget<_, _>>::OutputGadget::alloc(
                &mut cs.ns(|| "zero_commitment_gadget"),
                || Ok(*zero_commitment),
            )
            .unwrap();

        let blinded_commitment_gadget =
            <<Testnet2 as Network>::ValueCommitmentGadget as CommitmentGadget<_, _>>::OutputGadget::alloc(
                &mut cs.ns(|| "blinded_commitment_gadget"),
                || Ok(blinded_commitment),
            )
            .unwrap();

        let value_balance_bytes =
            UInt8::alloc_vec(cs.ns(|| "value_balance_bytes"), &(value_balance.0.unsigned_abs()).to_le_bytes()).unwrap();

        let is_negative =
            Boolean::alloc(&mut cs.ns(|| "value_balance_is_negative"), || Ok(value_balance.is_negative())).unwrap();

        let value_balance_comm = ValueBalanceCommitmentGadget::<Testnet2>::check_commitment_without_randomness_gadget(
            &mut cs.ns(|| "value_balance_commitment"),
            &commitment_scheme_gadget,
            &value_balance_bytes,
        )
        .unwrap();

        ValueBalanceCommitmentGadget::<Testnet2>::check_value_balance_commitment_gadget(
            &mut cs.ns(|| "verify_value_balance_commitment"),
            &partial_combined_commitments_gadget,
            &value_balance_comm,
            &is_negative,
            &c_gadget,
            &zero_commitment_gadget,
            &blinded_commitment_gadget,
        )
        .unwrap();

        if !cs.is_satisfied() {
            println!("which is unsatisfied: {:?}", cs.which_is_unsatisfied().unwrap());
        }
        assert!(cs.is_satisfied());
    }
}
