// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;

impl<N: Network> Process<N> {
    /// Executes the fee given the credits record, the fee amount (in microcredits),
    /// and the deployment or execution ID.
    #[inline]
    pub fn execute_fee<A: circuit::Aleo<Network = N>, R: Rng + CryptoRng>(
        &self,
        private_key: &PrivateKey<N>,
        credits: Record<N, Plaintext<N>>,
        fee_in_microcredits: u64,
        deployment_or_execution_id: Field<N>,
        rng: &mut R,
    ) -> Result<(Response<N>, Transition<N>, Trace<N>)> {
        let timer = timer!("Process::execute_fee");

        // Ensure the fee has the correct program ID.
        let program_id = ProgramID::from_str("credits.aleo")?;
        // Ensure the fee has the correct function.
        let function_name = Identifier::from_str("fee")?;

        // Retrieve the input types.
        let input_types = self.get_program(program_id)?.get_function(&function_name)?.input_types();
        // Prepare the fee in microcredits.
        let fee_in_microcredits = Value::from_str(&U64::<N>::new(fee_in_microcredits).to_string())?;
        // Prepare the deployment or execution ID.
        let deployment_or_execution_id = Value::from(Literal::Field(deployment_or_execution_id));
        // Construct the inputs.
        let inputs = [Value::Record(credits), fee_in_microcredits, deployment_or_execution_id];
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
        let _response = self.get_stack(program_id)?.execute_function::<A>(call_stack)?;
        lap!(timer, "Construct the authorization from the function");

        // Prepare the stack.
        let stack = self.get_stack(program_id)?;

        #[cfg(feature = "aleo-cli")]
        println!("{}", format!(" • Calling '{program_id}/{function_name}'...").dimmed());

        // Initialize the trace.
        let trace = Arc::new(RwLock::new(Trace::new()));
        // Initialize the call stack.
        let call_stack = CallStack::execute(authorization, trace.clone())?;
        // Execute the circuit.
        let response = stack.execute_function::<A>(call_stack)?;
        lap!(timer, "Execute the circuit");

        // Extract the trace.
        let trace = Arc::try_unwrap(trace).unwrap().into_inner();
        // Ensure the trace contains 1 transition.
        ensure!(
            trace.transitions().len() == 1,
            "Execution of '{program_id}/{function_name}' does not contain 1 transition"
        );

        finish!(timer);

        Ok((response, trace.transitions()[0].clone(), trace))
    }

    /// Verifies the given fee is valid.
    /// Note: This does *not* check that the global state root exists in the ledger.
    #[inline]
    pub fn verify_fee(&self, fee: &Fee<N>, deployment_or_execution_id: Field<N>) -> Result<()> {
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

        // Ensure there are exactly 3 inputs.
        ensure!(fee.inputs().len() == 3, "Incorrect number of inputs to the fee transition");
        // Ensure each input is valid.
        if fee.inputs().iter().enumerate().any(|(index, input)| !input.verify(function_id, fee.tcm(), index)) {
            bail!("Failed to verify a fee input")
        }
        // Retrieve the 3rd input as the candidate ID.
        let candidate_id = match fee.inputs().get(2) {
            Some(Input::Public(_, Some(Plaintext::Literal(Literal::Field(candidate_id), _)))) => *candidate_id,
            _ => bail!("Failed to get the deployment or execution ID in the fee transition"),
        };
        // Ensure the candidate ID is the deployment or execution ID.
        if candidate_id != deployment_or_execution_id {
            bail!("Incorrect deployment or execution ID in the fee transition")
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

        // Ensure the fee proof is valid.
        Trace::verify_fee_proof((verifying_key, vec![inputs]), fee)?;
        lap!(timer, "Verify the fee proof");

        finish!(timer);

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::block::Transaction;
    use snarkvm_utilities::TestRng;

    #[test]
    fn test_verify_fee() {
        let rng = &mut TestRng::default();
        // Fetch a deployment transaction.
        let deployment_transaction = crate::vm::test_helpers::sample_deployment_transaction(rng);

        // Construct a new process.
        let process = Process::load().unwrap();

        match deployment_transaction {
            Transaction::Deploy(_, _, deployment, fee) => {
                // Compute the deployment ID.
                let deployment_id = deployment.to_deployment_id().unwrap();

                assert!(process.verify_fee(&fee, deployment_id).is_ok());
            }
            _ => panic!("Expected a deployment transaction"),
        }
    }
}
