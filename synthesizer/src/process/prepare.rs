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

use circuit::Assignment;

use super::*;

impl<N: Network> Process<N> {
    /// Prepares a call to the program function for the given inputs.
    #[inline]
    pub fn prepare_function<A: circuit::Aleo<Network = N>>(
        &self,
        authorization: Authorization<N>,
    ) -> Result<(Response<N>, Execution<N>, Inclusion<N>, Vec<CallMetrics<N>>, Vec<Assignment<N::Field>>)> {
        let timer = timer!("Process::prepare");

        // Retrieve the main request (without popping it).
        let request = authorization.peek_next()?;

        #[cfg(feature = "aleo-cli")]
        println!("{}", format!(" • Executing '{}/{}'...", request.program_id(), request.function_name()).dimmed());

        // Initialize the execution.
        let execution = Arc::new(RwLock::new(Execution::new()));
        // Initialize the inclusion.
        let inclusion = Arc::new(RwLock::new(Inclusion::new()));
        // Initialize the metrics.
        let metrics = Arc::new(RwLock::new(Vec::new()));
        // Initialize the call stack.
        let assignments = Assignments::<N>::default();
        let call_stack = CallStack::prepare(
            authorization,
            execution.clone(),
            inclusion.clone(),
            metrics.clone(),
            assignments.clone(),
        )?;

        lap!(timer, "Initialize call stack");
        // Execute the circuit.
        let response = self.get_stack(request.program_id())?.execute_function::<A>(call_stack)?;
        lap!(timer, "Synthesize the circuit");
        // Extract the execution.
        let execution = Arc::try_unwrap(execution).unwrap().into_inner();
        // Ensure the execution is not empty.
        ensure!(!execution.is_empty(), "Execution of '{}/{}' is empty", request.program_id(), request.function_name());
        // Extract the inclusion.
        let inclusion = Arc::try_unwrap(inclusion).unwrap().into_inner();
        // Extract the metrics.
        let metrics = Arc::try_unwrap(metrics).unwrap().into_inner();
        // Extract the assignments.
        let assignments = Arc::try_unwrap(assignments).unwrap_or_default().into_inner();

        finish!(timer);
        Ok((response, execution, inclusion, metrics, assignments))
    }

    /// Prepares a fee for the given executions.
    #[inline]
    pub fn prepare_fee<A: circuit::Aleo<Network = N>, R: Rng + CryptoRng>(
        &self,
        private_key: &PrivateKey<N>,
        credits: Record<N, Plaintext<N>>,
        fee_in_microcredits: u64,
        rng: &mut R,
    ) -> Result<(Response<N>, Transition<N>, Inclusion<N>, Vec<Assignment<N::Field>>, Vec<CallMetrics<N>>)> {
        let timer = timer!("Process::prepare_fee");

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
        let _response = self.get_stack(program_id)?.execute_function::<A>(call_stack)?;
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
        let assignments = Assignments::<N>::default();
        // Pass registers to Callstack
        let call_stack = CallStack::prepare(
            authorization,
            execution.clone(),
            inclusion.clone(),
            metrics.clone(),
            assignments.clone(),
        )?;
        // Execute the circuit.
        let response = stack.execute_function::<A>(call_stack)?;
        lap!(timer, "Execute the circuit");

        // Extract the execution.
        let execution = Arc::try_unwrap(execution).unwrap().into_inner();
        // Ensure the execution contains 1 transition.
        ensure!(execution.len() == 1, "Execution of '{}/{}' does not contain 1 transition", program_id, function_name);
        // Extract the inclusion.
        let inclusion = Arc::try_unwrap(inclusion).unwrap().into_inner();
        // Extract the metrics.
        let metrics = Arc::try_unwrap(metrics).unwrap().into_inner();
        // Extract the assignments
        let assignments = Arc::try_unwrap(assignments).unwrap_or_default().into_inner();

        finish!(timer);

        Ok((response, execution.peek()?.clone(), inclusion, assignments, metrics))
    }
}
