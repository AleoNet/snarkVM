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
    /// Executes a program closure on the given inputs.
    ///
    /// # Errors
    /// This method will halt if the given inputs are not the same length as the input statements.
    #[inline]
    pub fn execute_closure<A: circuit::Aleo<Network = N>>(
        &self,
        closure: &Closure<N>,
        inputs: &[circuit::Value<A>],
        call_stack: CallStack<N>,
        caller: circuit::Address<A>,
        tvk: circuit::Field<A>,
    ) -> Result<Vec<circuit::Value<A>>> {
        let timer = timer!("Stack::execute_closure");

        // Ensure the call stack is not `Evaluate`.
        ensure!(!matches!(call_stack, CallStack::Evaluate(..)), "Illegal operation: cannot evaluate in execute mode");

        // Ensure the number of inputs matches the number of input statements.
        if closure.inputs().len() != inputs.len() {
            bail!("Expected {} inputs, found {}", closure.inputs().len(), inputs.len())
        }
        lap!(timer, "Check the number of inputs");

        // Retrieve the number of public variables in the circuit.
        let num_public = A::num_public();

        // Initialize the registers.
        let mut registers = Registers::new(call_stack, self.get_register_types(closure.name())?.clone());
        // Set the transition caller, as a circuit.
        registers.set_caller_circuit(caller);
        // Set the transition view key, as a circuit.
        registers.set_tvk_circuit(tvk);
        lap!(timer, "Initialize the registers");

        // Store the inputs.
        closure.inputs().iter().map(|i| i.register()).zip_eq(inputs).try_for_each(|(register, input)| {
            // If the circuit is in execute mode, then store the console input.
            if let CallStack::Execute(..) = registers.call_stack() {
                use circuit::Eject;
                // Assign the console input to the register.
                registers.store(self, register, input.eject_value())?;
            }
            // Assign the circuit input to the register.
            registers.store_circuit(self, register, input.clone())
        })?;
        lap!(timer, "Store the inputs");

        // Execute the instructions.
        for instruction in closure.instructions() {
            // If the circuit is in execute mode, then evaluate the instructions.
            if let CallStack::Execute(..) = registers.call_stack() {
                // If the evaluation fails, bail and return the error.
                if let Err(error) = instruction.evaluate(self, &mut registers) {
                    bail!("Failed to evaluate instruction ({instruction}): {error}");
                }
            }
            // Execute the instruction.
            instruction.execute(self, &mut registers)?;
        }
        lap!(timer, "Execute the instructions");

        // Ensure the number of public variables remains the same.
        ensure!(A::num_public() == num_public, "Illegal closure operation: instructions injected public variables");

        // Load the outputs.
        let outputs_iter = closure.outputs().iter().map(|output| {
            // Retrieve the circuit output from the register.
            registers.load_circuit(self, &Operand::Register(output.register().clone()))
        });
        let outputs = outputs_iter.collect();
        lap!(timer, "Load the outputs");

        finish!(timer);
        outputs
    }

    /// Executes a program function on the given inputs.
    ///
    /// Note: To execute a transition, do **not** call this method. Instead, call `Process::execute`.
    ///
    /// # Errors
    /// This method will halt if the given inputs are not the same length as the input statements.
    #[inline]
    pub fn execute_function<A: circuit::Aleo<Network = N>, R: Rng + CryptoRng>(
        &self,
        mut call_stack: CallStack<N>,
        rng: &mut R,
    ) -> Result<Response<N>> {
        let timer = timer!("Stack::execute_function");

        // Ensure the call stack is not `Evaluate`.
        ensure!(!matches!(call_stack, CallStack::Evaluate(..)), "Illegal operation: cannot evaluate in execute mode");

        // Ensure the circuit environment is clean.
        A::reset();

        // Retrieve the next request.
        let console_request = call_stack.pop()?;

        // Ensure the network ID matches.
        ensure!(
            **console_request.network_id() == N::ID,
            "Network ID mismatch. Expected {}, but found {}",
            N::ID,
            console_request.network_id()
        );

        // Retrieve the function from the program.
        let function = self.get_function(console_request.function_name())?;
        // Retrieve the number of inputs.
        let num_inputs = function.inputs().len();
        // Ensure the number of inputs matches the number of input statements.
        if num_inputs != console_request.inputs().len() {
            bail!("Expected {num_inputs} inputs, found {}", console_request.inputs().len())
        }
        // Retrieve the input types.
        let input_types = function.input_types();
        // Retrieve the output types.
        let output_types = function.output_types();
        lap!(timer, "Retrieve the input and output types");

        // Ensure the inputs match their expected types.
        console_request.inputs().iter().zip_eq(&input_types).try_for_each(|(input, input_type)| {
            // Ensure the input matches the input type in the function.
            self.matches_value_type(input, input_type)
        })?;
        lap!(timer, "Verify the input types");

        // Ensure the request is well-formed.
        ensure!(console_request.verify(&input_types), "Request is invalid");
        lap!(timer, "Verify the request");

        // Initialize the registers.
        let mut registers = Registers::new(call_stack, self.get_register_types(function.name())?.clone());

        use circuit::{Eject, Inject};

        // Inject the transition public key `tpk` as `Mode::Public`.
        let tpk = circuit::Group::<A>::new(circuit::Mode::Public, console_request.to_tpk());
        // Inject the request as `Mode::Private`.
        let request = circuit::Request::new(circuit::Mode::Private, console_request.clone());
        // Ensure the request has a valid signature, inputs, and transition view key.
        A::assert(request.verify(&input_types, &tpk));

        // Set the transition caller.
        registers.set_caller(*console_request.caller());
        // Set the transition caller, as a circuit.
        registers.set_caller_circuit(request.caller().clone());

        // Set the transition view key.
        registers.set_tvk(*console_request.tvk());
        // Set the transition view key, as a circuit.
        registers.set_tvk_circuit(request.tvk().clone());

        lap!(timer, "Initialize the registers");

        #[cfg(debug_assertions)]
        Self::log_circuit::<A, _>("Request");

        // Retrieve the number of constraints for verifying the request in the circuit.
        let num_request_constraints = A::num_constraints();

        // Retrieve the number of public variables in the circuit.
        let num_public = A::num_public();

        // Store the inputs.
        function.inputs().iter().map(|i| i.register()).zip_eq(request.inputs()).try_for_each(|(register, input)| {
            // If the circuit is in execute mode, then store the console input.
            if let CallStack::Execute(..) = registers.call_stack() {
                // Assign the console input to the register.
                registers.store(self, register, input.eject_value())?;
            }
            // Assign the circuit input to the register.
            registers.store_circuit(self, register, input.clone())
        })?;
        lap!(timer, "Store the inputs");

        // Initialize a tracker to determine if there are any function calls.
        let mut contains_function_call = false;

        // Execute the instructions.
        for instruction in function.instructions() {
            // If the circuit is in execute mode, then evaluate the instructions.
            if let CallStack::Execute(..) = registers.call_stack() {
                // If the evaluation fails, bail and return the error.
                if let Err(error) = instruction.evaluate(self, &mut registers) {
                    bail!("Failed to evaluate instruction ({instruction}): {error}");
                }
            }

            // Execute the instruction.
            instruction.execute(self, &mut registers)?;

            // If the instruction was a function call, then set the tracker to `true`.
            if let Instruction::Call(call) = instruction {
                // Check if the call is a function call.
                if call.is_function_call(self)? {
                    contains_function_call = true;
                }
            }
        }
        lap!(timer, "Execute the instructions");

        // Load the outputs.
        let output_registers = &function.outputs().iter().map(|output| output.register().clone()).collect::<Vec<_>>();
        let outputs = output_registers
            .iter()
            .map(|register| registers.load_circuit(self, &Operand::Register(register.clone())))
            .collect::<Result<Vec<_>>>()?;
        lap!(timer, "Load the outputs");

        #[cfg(debug_assertions)]
        Self::log_circuit::<A, _>(format!("Function '{}()'", function.name()));

        // Retrieve the number of constraints for executing the function in the circuit.
        let num_function_constraints = A::num_constraints().saturating_sub(num_request_constraints);

        // If the function does not contain function calls, ensure no new public variables were injected.
        if !contains_function_call {
            // Ensure the number of public variables remains the same.
            ensure!(A::num_public() == num_public, "Instructions in function injected public variables");
        }

        // Construct the response.
        let response = circuit::Response::from_outputs(
            request.network_id(),
            request.program_id(),
            request.function_name(),
            num_inputs,
            request.tvk(),
            request.tcm(),
            outputs,
            &output_types,
            output_registers,
        );
        lap!(timer, "Construct the response");

        #[cfg(debug_assertions)]
        Self::log_circuit::<A, _>("Response");

        // Retrieve the number of constraints for verifying the response in the circuit.
        let num_response_constraints =
            A::num_constraints().saturating_sub(num_request_constraints).saturating_sub(num_function_constraints);

        // If the circuit is in `Execute` mode, then prepare the 'finalize' scope if it exists.
        let finalize = if matches!(registers.call_stack(), CallStack::Synthesize(..))
            || matches!(registers.call_stack(), CallStack::CheckDeployment(..))
            || matches!(registers.call_stack(), CallStack::Execute(..))
        {
            // If this function has the finalize command, then construct the finalize inputs.
            if let Some(command) = function.finalize_command() {
                use circuit::ToBits;

                // Ensure the number of inputs is within bounds.
                ensure!(
                    command.operands().len() <= N::MAX_INPUTS,
                    "The 'finalize' command contains too many operands. The maximum number of inputs is {}.",
                    N::MAX_INPUTS
                );

                // Initialize a vector for the (console) finalize inputs.
                let mut console_finalize_inputs = Vec::with_capacity(command.operands().len());
                // Initialize a vector for the (circuit) finalize input bits.
                let mut circuit_finalize_input_bits = Vec::with_capacity(command.operands().len());

                // Retrieve the finalize inputs.
                for operand in command.operands() {
                    // Retrieve the finalize input.
                    let value = registers.load_circuit(self, operand)?;
                    // TODO (howardwu): Expand the scope of 'finalize' to support other register types.
                    //  See `RegisterTypes::initialize_function_types()` for the same set of checks.
                    // Ensure the value is a literal (for now).
                    match value {
                        circuit::Value::Plaintext(circuit::Plaintext::Literal(..)) => (),
                        circuit::Value::Plaintext(circuit::Plaintext::Struct(..)) => {
                            bail!(
                                "'{}/{}' attempts to pass an 'struct' into 'finalize'",
                                self.program_id(),
                                function.name()
                            );
                        }
                        circuit::Value::Record(..) => {
                            bail!(
                                "'{}/{}' attempts to pass a 'record' into 'finalize'",
                                self.program_id(),
                                function.name()
                            );
                        }
                    }

                    // Store the (console) finalize input.
                    console_finalize_inputs.push(value.eject_value());
                    // Store the (circuit) finalize input bits.
                    circuit_finalize_input_bits.extend(value.to_bits_le());
                }

                // Compute the finalize inputs checksum.
                let finalize_checksum = A::hash_bhp1024(&circuit_finalize_input_bits);
                // Inject the finalize inputs checksum as `Mode::Public`.
                let circuit_checksum = circuit::Field::<A>::new(circuit::Mode::Public, finalize_checksum.eject_value());
                // Enforce the injected checksum matches the original checksum.
                A::assert_eq(circuit_checksum, finalize_checksum);

                #[cfg(debug_assertions)]
                Self::log_circuit::<A, _>("Finalize");

                lap!(timer, "Construct the finalize inputs");

                // Return the (console) finalize inputs.
                Some(console_finalize_inputs)
            } else {
                None
            }
        } else {
            None
        };

        use circuit::{ToField, Zero};

        let mut i64_gates = circuit::I64::zero();
        let mut field_gates = circuit::Field::zero();

        // Increment the gates by the amount in each record input.
        for input in request.inputs() {
            match input {
                // Dereference the record gates to retrieve the u64 gates.
                circuit::Value::Record(record) => {
                    // Retrieve the record gates.
                    let record_gates = &**record.gates();
                    // Increment the i64 gates.
                    i64_gates += record_gates.clone().cast_as_dual();
                    // Increment the field gates.
                    field_gates += record_gates.to_field();
                }
                // Skip iterations that are not records.
                _ => continue,
            }
        }

        // Ensure the i64 gates matches the field gates.
        A::assert_eq(i64_gates.to_field(), &field_gates);

        // Decrement the gates by the amount in each record output.
        for output in response.outputs() {
            match output {
                // Dereference the gates to retrieve the u64 gates.
                circuit::Value::Record(record) => {
                    // Retrieve the record gates.
                    let record_gates = &**record.gates();
                    // Decrement the i64 gates.
                    i64_gates -= record_gates.clone().cast_as_dual();
                    // Decrement the field gates.
                    field_gates -= record_gates.to_field();
                }
                // Skip iterations that are not records.
                _ => continue,
            }
        }

        // If the program and function is not a coinbase function, then ensure the i64 gates is positive.
        if !Program::is_coinbase(self.program.id(), function.name()) {
            use circuit::MSB;

            // Ensure the i64 gates MSB is false.
            A::assert(!i64_gates.msb());
            // Ensure the i64 gates matches the field gates.
            A::assert_eq(i64_gates.to_field(), &field_gates);

            // Inject the field gates as `Mode::Public`.
            let public_gates = circuit::Field::<A>::new(circuit::Mode::Public, field_gates.eject_value());
            // Ensure the injected field gates matches.
            A::assert_eq(public_gates, field_gates);

            #[cfg(debug_assertions)]
            println!("Logging fee: {}", i64_gates.eject_value());
        } else {
            // Inject the field gates as `Mode::Public`.
            let public_gates = circuit::Field::<A>::new(circuit::Mode::Public, i64_gates.to_field().eject_value());
            // Ensure the injected i64 gates matches.
            A::assert_eq(public_gates, &i64_gates);
        }

        #[cfg(debug_assertions)]
        Self::log_circuit::<A, _>("Complete");

        lap!(timer, "Perform the fee operations");

        // Eject the fee.
        let fee = i64_gates.eject_value();
        // Eject the response.
        let response = response.eject_value();

        // Ensure the outputs matches the expected value types.
        response.outputs().iter().zip_eq(&output_types).try_for_each(|(output, output_type)| {
            // Ensure the output matches its expected type.
            self.matches_value_type(output, output_type)
        })?;

        // If the circuit is in `Execute` mode, then ensure the circuit is satisfied.
        if let CallStack::Execute(..) = registers.call_stack() {
            // If the circuit is empty or not satisfied, then throw an error.
            ensure!(
                A::num_constraints() > 0 && A::is_satisfied(),
                "'{}/{}' is not satisfied on the given inputs ({} constraints).",
                self.program.id(),
                function.name(),
                A::num_constraints()
            );
        }

        // Eject the circuit assignment and reset the circuit.
        let assignment = A::eject_assignment_and_reset();

        // If the circuit is in `Synthesize` or `Execute` mode, synthesize the circuit key, if it does not exist.
        if matches!(registers.call_stack(), CallStack::Synthesize(..))
            || matches!(registers.call_stack(), CallStack::Execute(..))
        {
            // If the proving key does not exist, then synthesize it.
            if !self.contains_proving_key(function.name()) {
                // Add the circuit key to the mapping.
                self.synthesize_from_assignment(function.name(), &assignment)?;
                lap!(timer, "Synthesize the {} circuit key", function.name());
            }
        }

        // If the circuit is in `CheckDeployment` mode, then save the assignment.
        if let CallStack::CheckDeployment(_, _, ref assignments) = registers.call_stack() {
            // Add the assignment to the assignments.
            assignments.write().push(assignment);
            lap!(timer, "Save the circuit assignment");
        }
        // If the circuit is in `Execute` mode, then execute the circuit into a transition.
        else if let CallStack::Execute(_, ref execution, ref inclusion, ref metrics) = registers.call_stack() {
            registers.ensure_console_and_circuit_registers_match()?;

            // Retrieve the proving key.
            let proving_key = self.get_proving_key(function.name())?;
            // Execute the circuit.
            let proof = match proving_key.prove(function.name(), &assignment, rng) {
                Ok(proof) => proof,
                Err(error) => bail!("Execution proof failed - {error}"),
            };
            lap!(timer, "Execute the circuit");

            // Construct the transition.
            let transition =
                Transition::from(&console_request, &response, finalize, &output_types, output_registers, proof, *fee)?;

            // Add the transition commitments.
            inclusion.write().insert_transition(console_request.input_ids(), &transition)?;
            // Add the transition to the execution.
            execution.write().push(transition);

            // Add the metrics.
            metrics.write().push(CallMetrics {
                program_id: *self.program_id(),
                function_name: *function.name(),
                num_instructions: function.instructions().len(),
                num_request_constraints,
                num_function_constraints,
                num_response_constraints,
            });
        }

        finish!(timer);

        // Return the response.
        Ok(response)
    }

    /// Prints the current state of the circuit.
    #[cfg(debug_assertions)]
    pub(crate) fn log_circuit<A: circuit::Aleo<Network = N>, S: Into<String>>(scope: S) {
        use colored::Colorize;

        // Determine if the circuit is satisfied.
        let is_satisfied = if A::is_satisfied() { "✅".green() } else { "❌".red() };
        // Determine the count.
        let (num_constant, num_public, num_private, num_constraints, num_gates) = A::count();

        // Print the log.
        println!(
            "{is_satisfied} {:width$} (Constant: {num_constant}, Public: {num_public}, Private: {num_private}, Constraints: {num_constraints}, Gates: {num_gates})",
            scope.into().bold(),
            width = 20
        );
    }
}
