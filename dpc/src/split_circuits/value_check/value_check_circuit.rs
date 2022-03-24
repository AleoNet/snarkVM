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

use crate::{Network, ValueBalanceCommitmentGadget, ValueCheckPrivateVariables, ValueCheckPublicVariables};
use snarkvm_gadgets::{
    bits::Boolean,
    integers::uint::UInt8,
    traits::{algorithms::CommitmentGadget, alloc::AllocGadget},
};
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSynthesizer, ConstraintSystem};
use snarkvm_utilities::ToBytes;

#[derive(Clone)]
pub struct ValueCheckCircuit<N: Network> {
    public: ValueCheckPublicVariables<N>,
    private: ValueCheckPrivateVariables<N>,
}

impl<N: Network> ValueCheckCircuit<N> {
    pub fn blank() -> Self {
        Self { public: ValueCheckPublicVariables::blank(), private: ValueCheckPrivateVariables::blank() }
    }

    pub fn new(public: ValueCheckPublicVariables<N>, private: ValueCheckPrivateVariables<N>) -> Self {
        Self { public, private }
    }
}

impl<N: Network> ConstraintSynthesizer<N::InnerScalarField> for ValueCheckCircuit<N> {
    fn generate_constraints<CS: ConstraintSystem<N::InnerScalarField>>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let public = &self.public;
        let private = &self.private;

        let value_balance_commitment = public.value_balance_commitment();

        let value_commitment_parameters = N::ValueCommitmentGadget::alloc_constant(
            &mut cs.ns(|| "Declare record value commitment parameters"),
            || Ok(N::value_commitment_scheme().clone()),
        )?;

        // *******************************************************************
        // Check that the value balance is valid by verifying the value balance commitment.
        // *******************************************************************

        // TODO (raychu86): Clean up this.
        let (c, partial_combined_commitments, _, _) = value_balance_commitment
            .gadget_verification_setup(
                &private.input_value_commitments,
                &private.output_value_commitments,
                &private.transition_id.to_bytes_le()?,
            )
            .unwrap();

        let c_gadget = <N::ValueCommitmentGadget as CommitmentGadget<
                N::ValueCommitmentScheme,
                N::InnerScalarField,
            >>::RandomnessGadget::alloc(&mut cs.ns(|| "c"), || Ok(&c))?;

        let partial_combined_commitments_gadget = <N::ValueCommitmentGadget as CommitmentGadget<
            N::ValueCommitmentScheme,
            N::InnerScalarField,
        >>::OutputGadget::alloc(
            &mut cs.ns(|| "Partially combined commitments"),
            || Ok(partial_combined_commitments),
        )?;

        let zero_commitment_gadget = <N::ValueCommitmentGadget as CommitmentGadget<
            N::ValueCommitmentScheme,
            N::InnerScalarField,
        >>::OutputGadget::alloc_input(
            &mut cs.ns(|| "Zero commitment gadget"),
            || Ok(*value_balance_commitment.commitment),
        )?;

        let blinding_factor_gadget = <N::ValueCommitmentGadget as CommitmentGadget<
            N::ValueCommitmentScheme,
            N::InnerScalarField,
        >>::RandomnessGadget::alloc_input(
            &mut cs.ns(|| "Blinding factor gadget"),
            || Ok(value_balance_commitment.blinding_factor),
        )?;

        let zero_bytes = UInt8::alloc_vec(cs.ns(|| "Zero"), &0i64.to_le_bytes())?;
        let blinded_commitment_gadget = value_commitment_parameters.check_commitment_gadget(
            &mut cs.ns(|| "Compute blinding commitment"),
            &zero_bytes,
            &blinding_factor_gadget,
        )?;

        let value_balance_bytes =
            UInt8::alloc_vec(cs.ns(|| "value_balance_bytes"), &(public.value_balance().0.abs() as u64).to_le_bytes())?;

        let is_negative =
            Boolean::alloc(&mut cs.ns(|| "Value balance is negative"), || Ok(public.value_balance().is_negative()))?;

        let value_balance_comm = ValueBalanceCommitmentGadget::<N>::check_commitment_without_randomness_gadget(
            &mut cs.ns(|| "Commitment on value balance without randomness"),
            &value_commitment_parameters,
            &value_balance_bytes,
        )?;

        ValueBalanceCommitmentGadget::<N>::check_value_balance_commitment_gadget(
            &mut cs.ns(|| "Verify value balance commitment"),
            &partial_combined_commitments_gadget,
            &value_balance_comm,
            &is_negative,
            &c_gadget,
            &zero_commitment_gadget,
            &blinded_commitment_gadget,
        )?;

        Ok(())
    }
}
