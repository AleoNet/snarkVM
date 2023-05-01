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

impl<N: Network> Process<N> {
    /// Executes the fee given the credits record and the fee amount (in microcredits).
    #[inline]
    pub fn execute_fee<A: circuit::Aleo<Network = N>, R: Rng + CryptoRng>(
        &self,
        private_key: &PrivateKey<N>,
        credits: Record<N, Plaintext<N>>,
        fee_in_microcredits: u64,
        rng: &mut R,
    ) -> Result<(Response<N>, Transition<N>, Inclusion<N>, Vec<CallMetrics<N>>)> {
        let timer = timer!("Process::execute_fee");

        // Ensure the fee has the correct program ID.
        let program_id = ProgramID::from_str("credits.aleo")?;
        // Ensure the fee has the correct function.
        let function_name = Identifier::from_str("fee")?;

        // Retrieve the input types.
        let input_types = self.get_program(program_id)?.get_function(&function_name)?.input_types();
        // Construct the inputs.
        let inputs = [Value::Record(credits), Value::from_str(&U64::<N>::new(fee_in_microcredits).to_string())?];
        lap!(timer, "Construct the inputs");
        // Compute the request.
        let request = Request::sign(private_key, program_id, function_name, inputs.iter(), &input_types, rng)?;
        lap!(timer, "Compute the request");
        // Initialize the authorization.
        let authorization = Authorization::new(&[request.clone()]);
        lap!(timer, "Initialize the authorization");
        // Construct the call stack.
        let call_stack = CallStack::Authorize(vec![request], *private_key, authorization.clone());
        // Construct the authorization from the function.
        let _response = self.get_stack(program_id)?.execute_function::<A, R>(call_stack, rng)?;
        lap!(timer, "Construct the authorization from the function");

        // Retrieve the main request (without popping it).
        let request = authorization.peek_next()?;
        // Prepare the stack.
        let stack = self.get_stack(request.program_id())?;

        #[cfg(feature = "aleo-cli")]
        println!("{}", format!(" • Calling '{}/{}'...", request.program_id(), request.function_name()).dimmed());

        // Initialize the execution.
        let execution = Arc::new(RwLock::new(Execution::new()));
        // Initialize the inclusion.
        let inclusion = Arc::new(RwLock::new(Inclusion::new()));
        // Initialize the metrics.
        let metrics = Arc::new(RwLock::new(Vec::new()));
        // Initialize the call stack.
        let call_stack = CallStack::execute(authorization, execution.clone(), inclusion.clone(), metrics.clone())?;
        // Execute the circuit.
        let response = stack.execute_function::<A, R>(call_stack, rng)?;
        lap!(timer, "Execute the circuit");

        // Extract the execution.
        let execution = Arc::try_unwrap(execution).unwrap().into_inner();
        // Ensure the execution contains 1 transition.
        ensure!(execution.len() == 1, "Execution of '{}/{}' does not contain 1 transition", program_id, function_name);
        // Extract the inclusion.
        let inclusion = Arc::try_unwrap(inclusion).unwrap().into_inner();
        // Extract the metrics.
        let metrics = Arc::try_unwrap(metrics).unwrap().into_inner();

        finish!(timer);

        Ok((response, execution.peek()?.clone(), inclusion, metrics))
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

        // Ensure the inclusion proof is valid.
        Inclusion::verify_fee(fee)?;
        lap!(timer, "Verify the inclusion proof");

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
        // Ensure the transition proof is valid.
        ensure!(
            verifying_key.verify(function.name(), &inputs, fee.proof()),
            "Fee is invalid - failed to verify transition proof"
        );
        lap!(timer, "Verify the transition proof");

        finish!(timer);

        Ok(())
    }
}
