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
    /// Executes the given authorization.
    #[inline]
    pub fn execute<A: circuit::Aleo<Network = N>>(
        &self,
        authorization: Authorization<N>,
    ) -> Result<(Response<N>, Trace<N>)> {
        let timer = timer!("Process::execute");

        // Retrieve the main request (without popping it).
        let request = authorization.peek_next()?;
        // Construct the locator.
        let locator = Locator::new(*request.program_id(), *request.function_name());

        #[cfg(feature = "aleo-cli")]
        println!("{}", format!(" • Executing '{locator}'...",).dimmed());

        // Initialize the trace.
        let trace = Arc::new(RwLock::new(Trace::new()));
        // Initialize the call stack.
        let call_stack = CallStack::execute(authorization, trace.clone())?;
        lap!(timer, "Initialize call stack");

        // Execute the circuit.
        let response = self.get_stack(request.program_id())?.execute_function::<A>(call_stack)?;
        lap!(timer, "Execute the function");

        // Extract the trace.
        let trace = Arc::try_unwrap(trace).unwrap().into_inner();
        // Ensure the trace is not empty.
        ensure!(!trace.transitions().is_empty(), "Execution of '{locator}' is empty");

        finish!(timer);
        Ok((response, trace))
    }
}
