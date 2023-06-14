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
}
