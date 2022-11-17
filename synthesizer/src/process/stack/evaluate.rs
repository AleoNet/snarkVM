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

impl<N: Network> Stack<N> {
    /// Evaluates a program closure on the given inputs.
    ///
    /// # Errors
    /// This method will halt if the given inputs are not the same length as the input statements.
    #[inline]
    pub fn evaluate_closure<A: circuit::Aleo<Network = N>>(
        &self,
        closure: &Closure<N>,
        inputs: &[Value<N>],
        call_stack: CallStack<N>,
        caller: Address<N>,
        tvk: Field<N>,
    ) -> Result<Vec<Value<N>>> {
        let timer = timer!("Stack::evaluate_closure");

        // Ensure the number of inputs matches the number of input statements.
        if closure.inputs().len() != inputs.len() {
            bail!("Expected {} inputs, found {}", closure.inputs().len(), inputs.len())
        }

        // Initialize the registers.
        let mut registers = Registers::<N, A>::new(call_stack, self.get_register_types(closure.name())?.clone());
        // Set the transition caller.
        registers.set_caller(caller);
        // Set the transition view key.
        registers.set_tvk(tvk);
        lap!(timer, "Initialize the registers");

        // Store the inputs.
        closure.inputs().iter().map(|i| i.register()).zip_eq(inputs).try_for_each(|(register, input)| {
            // Assign the input value to the register.
            registers.store(self, register, input.clone())
        })?;
        lap!(timer, "Store the inputs");

        // Evaluate the instructions.
        for instruction in closure.instructions() {
            // If the evaluation fails, bail and return the error.
            if let Err(error) = instruction.evaluate(self, &mut registers) {
                bail!("Failed to evaluate instruction ({instruction}): {error}");
            }
        }
        lap!(timer, "Evaluate the instructions");

        // Load the outputs.
        let outputs_iter = closure.outputs().iter().map(|output| {
            // Retrieve the stack value from the register.
            registers.load(self, &Operand::Register(output.register().clone()))
        });
        let outputs = outputs_iter.collect();
        lap!(timer, "Load the outputs");

        finish!(timer);
        outputs
    }

    /// Evaluates a program function on the given inputs.
    ///
    /// # Errors
    /// This method will halt if the given inputs are not the same length as the input statements.
    #[inline]
    pub fn evaluate_function<A: circuit::Aleo<Network = N>>(&self, call_stack: CallStack<N>) -> Result<Response<N>> {
        let timer = timer!("Stack::evaluate_function");

        // Retrieve the next request, based on the call stack mode.
        let (request, call_stack) = match &call_stack {
            CallStack::Evaluate(authorization) => (authorization.next()?, call_stack),
            CallStack::Execute(authorization, ..) => (authorization.peek_next()?, call_stack.replicate()),
            _ => bail!("Illegal operation: call stack must be `Evaluate` or `Execute` in `evaluate_function`."),
        };
        lap!(timer, "Retrieve the next request");

        // Ensure the network ID matches.
        ensure!(
            **request.network_id() == N::ID,
            "Network ID mismatch. Expected {}, but found {}",
            N::ID,
            request.network_id()
        );

        // Retrieve the function, inputs, and transition view key.
        let function = self.get_function(request.function_name())?;
        let inputs = request.inputs();
        let caller = *request.caller();
        let tvk = *request.tvk();

        // Ensure the number of inputs matches.
        if function.inputs().len() != inputs.len() {
            bail!(
                "Function '{}' in the program '{}' expects {} inputs, but {} were provided.",
                function.name(),
                self.program.id(),
                function.inputs().len(),
                inputs.len()
            )
        }
        lap!(timer, "Perform input checks");

        // Initialize the registers.
        let mut registers = Registers::<N, A>::new(call_stack, self.get_register_types(function.name())?.clone());
        // Set the transition caller.
        registers.set_caller(caller);
        // Set the transition view key.
        registers.set_tvk(tvk);
        lap!(timer, "Initialize the registers");

        // Ensure the request is well-formed.
        ensure!(request.verify(&function.input_types()), "Request is invalid");
        lap!(timer, "Verify the request");

        // Store the inputs.
        function.inputs().iter().map(|i| i.register()).zip_eq(inputs).try_for_each(|(register, input)| {
            // Assign the input value to the register.
            registers.store(self, register, input.clone())
        })?;
        lap!(timer, "Store the inputs");

        // Evaluate the instructions.
        for instruction in function.instructions() {
            // If the evaluation fails, bail and return the error.
            if let Err(error) = instruction.evaluate(self, &mut registers) {
                bail!("Failed to evaluate instruction ({instruction}): {error}");
            }
        }
        lap!(timer, "Evaluate the instructions");

        // Retrieve the output registers.
        let output_registers = &function.outputs().iter().map(|output| output.register().clone()).collect::<Vec<_>>();
        lap!(timer, "Retrieve the output registers");

        // Load the outputs.
        let outputs = output_registers
            .iter()
            .map(|register| {
                // Retrieve the stack value from the register.
                registers.load(self, &Operand::Register(register.clone()))
            })
            .collect::<Result<Vec<_>>>()?;
        lap!(timer, "Load the outputs");

        finish!(timer);

        // Compute the response.
        Response::new(
            request.network_id(),
            self.program.id(),
            function.name(),
            request.inputs().len(),
            request.tvk(),
            request.tcm(),
            outputs,
            &function.output_types(),
            output_registers,
        )
    }
}
