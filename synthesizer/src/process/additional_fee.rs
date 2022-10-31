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

use super::*;

impl<N: Network> Process<N> {
    /// Returns an additional fee given the credits record and the additional fee amount (in gates).
    #[inline]
    pub fn execute_additional_fee<A: circuit::Aleo<Network = N>, R: Rng + CryptoRng>(
        &self,
        private_key: &PrivateKey<N>,
        credits: Record<N, Plaintext<N>>,
        state_path: StatePath<N>,
        additional_fee_in_gates: u64,
        rng: &mut R,
    ) -> Result<(Response<N>, AdditionalFee<N>)> {
        // Ensure the additional fee has the correct program ID.
        let program_id = ProgramID::from_str("credits.aleo")?;
        // Ensure the additional fee has the correct function.
        let function_name = Identifier::from_str("fee")?;

        // Retrieve the input types.
        let input_types = self.get_program(&program_id)?.get_function(&function_name)?.input_types();
        // Construct the inputs.
        let inputs =
            vec![Value::Record(credits), Value::from_str(&format!("{}", U64::<N>::new(additional_fee_in_gates)))?];
        // Compute the request.
        let request = Request::sign(private_key, program_id, function_name, &inputs, &input_types, rng)?;
        // Initialize the authorization.
        let mut authorization = Authorization::new(&[request.clone()]);
        // Add the state path to the authorization.
        authorization.insert_state_path(state_path.transition_leaf().id(), state_path);
        // Construct the call stack.
        let call_stack = CallStack::Authorize(vec![request], *private_key, authorization.clone());
        // Construct the authorization from the function.
        let _response = self.get_stack(&program_id)?.execute_function::<A, R>(call_stack, rng)?;

        // Retrieve the main request (without popping it).
        let request = authorization.peek_next()?;
        // Prepare the stack.
        let stack = self.get_stack(request.program_id())?;

        #[cfg(feature = "aleo-cli")]
        println!("{}", format!(" • Calling '{}/{}'...", request.program_id(), request.function_name()).dimmed());

        // Initialize the execution.
        let execution = Arc::new(RwLock::new(Execution::new()));
        // Execute the circuit.
        let response = stack.execute_function::<A, R>(CallStack::execute(authorization, execution.clone())?, rng)?;
        // Extract the execution.
        let execution = execution.read().clone();
        // Ensure the execution contains 1 transition.
        ensure!(execution.len() == 1, "Execution of '{}/{}' does not contain 1 transition", program_id, function_name);

        Ok((response, execution.peek()?.clone()))
    }

    /// Verifies the given additional fee is valid.
    #[inline]
    pub fn verify_additional_fee(&self, additional_fee: &AdditionalFee<N>) -> Result<()> {
        #[cfg(debug_assertions)]
        println!("Verifying additional fee for {}/{}...", additional_fee.program_id(), additional_fee.function_name());

        // Ensure the additional fee has the correct program ID.
        let fee_program_id = ProgramID::from_str("credits.aleo")?;
        ensure!(*additional_fee.program_id() == fee_program_id, "Incorrect program ID for additional fee");

        // Ensure the additional fee has the correct function.
        let fee_function = Identifier::from_str("fee")?;
        ensure!(*additional_fee.function_name() == fee_function, "Incorrect function name for additional fee");

        // Ensure the transition ID of the additional fee is correct.
        ensure!(**additional_fee.id() == additional_fee.to_root()?, "Transition ID of the additional fee is incorrect");

        // Ensure the number of inputs is within the allowed range.
        ensure!(additional_fee.inputs().len() <= N::MAX_INPUTS, "Additional fee exceeded maximum number of inputs");
        // Ensure the number of outputs is within the allowed range.
        ensure!(additional_fee.outputs().len() <= N::MAX_INPUTS, "Additional fee exceeded maximum number of outputs");

        // Compute the function ID as `Hash(network_id, program_id, function_name)`.
        let function_id = N::hash_bhp1024(
            &(
                U16::<N>::new(N::ID),
                additional_fee.program_id().name(),
                additional_fee.program_id().network(),
                additional_fee.function_name(),
            )
                .to_bits_le(),
        )?;

        // Ensure each input is valid.
        if additional_fee
            .inputs()
            .iter()
            .enumerate()
            .any(|(index, input)| !input.verify(function_id, additional_fee.tcm(), index))
        {
            bail!("Failed to verify an additional fee input")
        }
        // Ensure each output is valid.
        let num_inputs = additional_fee.inputs().len();
        if additional_fee
            .outputs()
            .iter()
            .enumerate()
            .any(|(index, output)| !output.verify(function_id, additional_fee.tcm(), num_inputs + index))
        {
            bail!("Failed to verify an additional fee output")
        }

        // Ensure the fee is not negative.
        ensure!(additional_fee.fee() >= &0, "The fee must be zero or positive");

        // Compute the x- and y-coordinate of `tpk`.
        let (tpk_x, tpk_y) = additional_fee.tpk().to_xy_coordinate();

        // Construct the public inputs to verify the proof.
        let mut inputs = vec![N::Field::one(), *tpk_x, *tpk_y, **additional_fee.tcm()];
        // Extend the inputs with the input IDs.
        inputs.extend(additional_fee.inputs().iter().flat_map(|input| input.verifier_inputs()));
        // Extend the inputs with the output IDs.
        inputs.extend(additional_fee.outputs().iter().flat_map(|output| output.verifier_inputs()));
        // Extend the inputs with the fee.
        inputs.push(*I64::<N>::new(*additional_fee.fee()).to_field()?);

        // Retrieve the stack.
        let stack = self.get_stack(additional_fee.program_id())?;
        // Retrieve the function from the stack.
        let function = stack.get_function(additional_fee.function_name())?;
        // Ensure the number of function calls in this function is 1.
        if stack.get_number_of_calls(function.name())? != 1 {
            bail!("The number of function calls in '{}/{}' should be 1", stack.program_id(), function.name())
        }

        #[cfg(debug_assertions)]
        println!("Additional fee public inputs ({} elements): {:#?}", inputs.len(), inputs);

        match additional_fee.proof() {
            TransitionProof::Birth(_) => bail!("The state path proof is missing from additional fee."),
            TransitionProof::BirthAndDeath { execution_proof, state_path_proof } => {
                // Ensure the additional fee contains input records.
                ensure!(
                    additional_fee.inputs().iter().any(|input| matches!(input, Input::Record(..))),
                    "The additional fee proof is the wrong type (found *no* input records)"
                );

                // Retrieve the verifying key.
                let verifying_key = self.get_verifying_key(stack.program_id(), function.name())?;

                // Ensure the execution proof is valid.
                ensure!(
                    verifying_key.verify(function.name(), &inputs, execution_proof),
                    "Additional fee is invalid - failed to verify execution proof"
                );

                // Retrieve the state path inputs for the additional fee.
                let mut state_path_verifier_inputs = vec![];
                for input in additional_fee.inputs() {
                    if let Input::Record(serial_number, _, origin) = input {
                        state_path_verifier_inputs.push(origin.verifier_inputs(serial_number));
                    }
                }
                ensure!(
                    state_path_verifier_inputs.len() == 1,
                    "The number of state path inputs for the additional fee is incorrect"
                );

                // TODO (howardwu): Cache this in the process.
                // Load the state path verifying key.
                let state_path_verifying_key = VerifyingKey::from_bytes_le(N::state_path_verifying_key_bytes())?;
                // Ensure the state path proof is valid.
                ensure!(
                    state_path_verifying_key.verify_batch(
                        STATE_PATH_FUNCTION_NAME,
                        &state_path_verifier_inputs,
                        state_path_proof
                    ),
                    "Transition state path is invalid."
                );
            }
        }

        Ok(())
    }
}
