// Copyright (C) 2019-2023 Aleo Systems Inc.
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
use crate::{Key, KeyBatch, KeyMode};

impl<N: Network> Process<N> {
    /// Executes the given fee.
    #[inline]
    pub fn execute_fee<A: circuit::Aleo<Network = N>, R: Rng + CryptoRng>(
        &self,
        fee: &mut Fee<N>,
        fee_assignments: &Vec<&Assignment<N::Field>>,
        inclusion_assignments: Option<Vec<&Assignment<N::Field>>>,
        rng: &mut R,
    ) -> Result<()> {
        let timer = timer!("Process::execute_fee");

        let fee_program_id = fee.transition().program_id();
        let fee_function_name = *fee.transition().function_name();
        let inclusion_name = Identifier::<N>::from_str(N::INCLUSION_FUNCTION_NAME)?;

        // Ensure the fee has the correct program ID.
        let fee_program_id_test = ProgramID::from_str("credits.aleo")?;
        ensure!(*fee_program_id == fee_program_id_test, "Incorrect program ID for fee");

        // Ensure the fee has the correct function.
        let fee_function = Identifier::from_str("fee")?;
        ensure!(fee_function_name == fee_function, "Incorrect function name for fee");

        // Ensure the assignments are not empty.
        if fee_assignments.is_empty() {
            bail!("Expected the assignments for the fee to *not* be empty")
        }

        let mut batch = KeyBatch::new(2, KeyMode::Proving);
        let mut assignments = Vec::with_capacity(2);
        let mut function_names = Vec::with_capacity(2);
        let proving_key = self.get_proving_key(fee_program_id, fee_function_name)?;
        batch.add(Key::ProvingKey(proving_key))?;
        assignments.push(fee_assignments);
        function_names.push(&fee_function_name);

        if let Some(inclusion_assignments) = inclusion_assignments.as_ref() {
            let proving_key = ProvingKey::<N>::new(N::inclusion_proving_key().clone());
            batch.add(Key::ProvingKey(proving_key))?;
            assignments.push(inclusion_assignments);
            function_names.push(&inclusion_name);
        }

        fee.prove(batch, assignments.as_slice(), function_names, rng)?;

        finish!(timer);
        Ok(())
    }

    /// Verifies the given fee is valid.
    /// Note: This does *not* check that the global state root exists in the ledger.
    #[inline]
    pub fn verify_fee(&self, fee: &Fee<N>) -> Result<()> {
        let timer = timer!("Process::verify_fee");

        #[cfg(debug_assertions)]
        println!("Verifying fee from {}/{}...", fee.program_id(), fee.function_name());

        // Ensure the fee has the correct program ID.
        let fee_program_id = ProgramID::from_str("credits.aleo")?;
        ensure!(*fee.program_id() == fee_program_id, "Incorrect program ID for fee");

        // Ensure the fee has the correct function.
        let fee_function = Identifier::from_str("fee")?;
        ensure!(*fee.function_name() == fee_function, "Incorrect function name for fee");

        // Ensure the transition ID of the fee is correct.
        ensure!(**fee.id() == fee.to_root()?, "Transition ID of the fee is incorrect");

        // Ensure the number of inputs is within the allowed range.
        ensure!(fee.inputs().len() <= N::MAX_INPUTS, "Fee exceeded maximum number of inputs");
        // Ensure the number of outputs is within the allowed range.
        ensure!(fee.outputs().len() <= N::MAX_INPUTS, "Fee exceeded maximum number of outputs");

        // Compute the function ID as `Hash(network_id, program_id, function_name)`.
        let function_id = N::hash_bhp1024(
            &(U16::<N>::new(N::ID), fee.program_id().name(), fee.program_id().network(), fee.function_name())
                .to_bits_le(),
        )?;

        // Ensure each input is valid.
        if fee.inputs().iter().enumerate().any(|(index, input)| !input.verify(function_id, fee.tcm(), index)) {
            bail!("Failed to verify a fee input")
        }
        lap!(timer, "Verify the inputs");

        // We need to verify 2 parts: the transition and inclusion
        let mut batch = KeyBatch::<N>::new(2, KeyMode::Verifying);
        let mut all_inputs = Vec::with_capacity(2);

        // Ensure each output is valid.
        let num_inputs = fee.inputs().len();
        if fee
            .outputs()
            .iter()
            .enumerate()
            .any(|(index, output)| !output.verify(function_id, fee.tcm(), num_inputs + index))
        {
            bail!("Failed to verify a fee output")
        }
        lap!(timer, "Verify the outputs");

        // Compute the x- and y-coordinate of `tpk`.
        let (tpk_x, tpk_y) = fee.tpk().to_xy_coordinates();

        // Construct the public inputs to verify the proof.
        let mut inputs = vec![N::Field::one(), *tpk_x, *tpk_y, **fee.tcm()];
        // Extend the inputs with the input IDs.
        inputs.extend(fee.inputs().iter().flat_map(|input| input.verifier_inputs()));
        // Extend the inputs with the output IDs.
        inputs.extend(fee.outputs().iter().flat_map(|output| output.verifier_inputs()));
        lap!(timer, "Construct the verifier inputs");

        // Retrieve the stack.
        let stack = self.get_stack(fee.program_id())?;
        // Retrieve the function from the stack.
        let function = stack.get_function(fee.function_name())?;
        // Ensure the number of function calls in this function is 1.
        if stack.get_number_of_calls(function.name())? != 1 {
            bail!("The number of function calls in '{}/{}' should be 1", stack.program_id(), function.name())
        }

        #[cfg(debug_assertions)]
        println!("Fee public inputs ({} elements): {:#?}", inputs.len(), inputs);

        // Ensure the fee contains input records.
        ensure!(
            fee.inputs().iter().any(|input| matches!(input, Input::Record(..))),
            "The fee proof is the wrong type (found *no* input records)"
        );

        // Retrieve the verifying key.
        let verifying_key = self.get_verifying_key(stack.program_id(), function.name())?;
        batch.add(Key::VerifyingKey(verifying_key))?;
        all_inputs.push(vec![inputs]);

        // Get inclusion proof vk and inputs.
        if fee.proves_inclusion() {
            let (inclusion_vk, inclusion_inputs) = Inclusion::prepare_verify_fee(fee)?;
            batch.add(Key::VerifyingKey(inclusion_vk))?;
            all_inputs.push(inclusion_inputs);
        }
        lap!(timer, "Get the inclusion proof vk and inputs");

        // Ensure there is a proof.
        let proof = fee.proof();
        ensure!(proof.is_some(), "Fee is invalid - missing proof");

        ensure!(fee.verify(batch, all_inputs.as_slice())?, "Fee is invalid - failed to verify proof");

        lap!(timer, "Verify the transition proof");

        finish!(timer);

        Ok(())
    }
}
