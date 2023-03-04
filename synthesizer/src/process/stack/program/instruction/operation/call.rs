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

impl<N: Network> Stack<N> {
    /// Evaluates the call instruction.
    #[inline]
    pub fn evaluate_call<A: circuit::Aleo<Network = N>>(
        &self,
        call: &Call<N>,
        registers: &mut Registers<N, A>,
    ) -> Result<()> {
        // Load the operands values.
        let inputs: Vec<_> = call.operands().iter().map(|operand| registers.load(&self, operand)).try_collect()?;

        // Retrieve the substack and resource.
        let (substack, resource) = match &call.operator() {
            // Retrieve the call stack and resource from the locator.
            CallOperator::Locator(locator) => {
                (self.get_external_stack(locator.program_id())?.clone(), locator.resource())
            }
            CallOperator::Resource(resource) => {
                // TODO (howardwu): Revisit this decision to forbid calling internal functions. A record cannot be spent again.
                //  But there are legitimate uses for passing a record through to an internal function.
                //  We could invoke the internal function without a state transition, but need to match visibility.
                if self.program().contains_function(resource) {
                    bail!("Cannot call '{resource}'. Use a closure ('closure {resource}:') instead.")
                }

                (self.clone(), resource)
            }
        };

        // If the operator is a closure, retrieve the closure and compute the output.
        let outputs = if let Ok(closure) = substack.program().get_closure(resource) {
            // Ensure the number of inputs matches the number of input statements.
            if closure.inputs().len() != inputs.len() {
                bail!("Expected {} inputs, found {}", closure.inputs().len(), inputs.len())
            }
            // Evaluate the closure, and load the outputs.
            substack.evaluate_closure::<A>(
                &closure,
                &inputs,
                registers.call_stack(),
                registers.caller()?,
                registers.tvk()?,
            )?
        }
        // If the operator is a function, retrieve the function and compute the output.
        else if let Ok(function) = substack.program().get_function(resource) {
            // Ensure the number of inputs matches the number of input statements.
            if function.inputs().len() != inputs.len() {
                bail!("Expected {} inputs, found {}", function.inputs().len(), inputs.len())
            }
            // Evaluate the function.
            let response = substack.evaluate_function::<A>(registers.call_stack())?;
            // Load the outputs.
            response.outputs().to_vec()
        }
        // Else, throw an error.
        else {
            bail!("Call operator '{}' is invalid or unsupported.", call.operator())
        };

        // Assign the outputs to the destination registers.
        for (output, register) in outputs.into_iter().zip_eq(&call.destinations()) {
            // Assign the output to the register.
            registers.store(self, register, output)?;
        }

        Ok(())
    }

    /// Executes the call instruction.
    #[inline]
    pub fn execute_call<A: circuit::Aleo<Network = N>>(
        &self,
        call: &Call<N>,
        registers: &mut Registers<N, A>,
    ) -> Result<()> {
        // Load the operands values.
        let inputs: Vec<_> =
            call.operands().iter().map(|operand| registers.load_circuit(self, operand)).try_collect()?;

        // Retrieve the substack and resource.
        let (substack, resource) = match call.operator() {
            // Retrieve the call stack and resource from the locator.
            CallOperator::Locator(locator) => {
                (self.get_external_stack(locator.program_id())?.clone(), locator.resource())
            }
            CallOperator::Resource(resource) => {
                // TODO (howardwu): Revisit this decision to forbid calling internal functions. A record cannot be spent again.
                //  But there are legitimate uses for passing a record through to an internal function.
                //  We could invoke the internal function without a state transition, but need to match visibility.
                if self.program().contains_function(resource) {
                    bail!("Cannot call '{resource}'. Use a closure ('closure {resource}:') instead.")
                }

                (self.clone(), resource)
            }
        };

        // If the operator is a closure, retrieve the closure and compute the output.
        let outputs = if let Ok(closure) = substack.program().get_closure(resource) {
            // Execute the closure, and load the outputs.
            substack.execute_closure(
                &closure,
                &inputs,
                registers.call_stack(),
                registers.caller_circuit()?,
                registers.tvk_circuit()?,
            )?
        }
        // If the operator is a function, retrieve the function and compute the output.
        else if let Ok(function) = substack.program().get_function(resource) {
            // Retrieve the number of inputs.
            let num_inputs = function.inputs().len();
            // Ensure the number of inputs matches the number of input statements.
            if num_inputs != inputs.len() {
                bail!("Expected {} inputs, found {}", num_inputs, inputs.len())
            }

            // Retrieve the number of public variables in the circuit.
            let num_public = A::num_public();

            use circuit::Eject;
            // Eject the existing circuit.
            let r1cs = A::eject_r1cs_and_reset();
            let (request, response) = {
                // Eject the circuit inputs.
                let inputs = inputs.eject_value();

                // Initialize an RNG.
                let rng = &mut rand::thread_rng();

                match registers.call_stack() {
                    // If the circuit is in authorize or synthesize mode, then add any external calls to the stack.
                    CallStack::Authorize(_, private_key, authorization)
                    | CallStack::Synthesize(_, private_key, authorization) => {
                        // Compute the request.
                        let request = Request::sign(
                            &private_key,
                            *substack.program_id(),
                            *function.name(),
                            inputs.iter(),
                            &function.input_types(),
                            rng,
                        )?;

                        // Retrieve the call stack.
                        let mut call_stack = registers.call_stack();
                        // Push the request onto the call stack.
                        call_stack.push(request.clone())?;

                        // Add the request to the authorization.
                        authorization.push(request.clone());

                        // Execute the request.
                        let response = substack.execute_function::<A, _>(call_stack, rng)?;

                        // Return the request and response.
                        (request, response)
                    }
                    CallStack::CheckDeployment(_, private_key, ..) => {
                        // Compute the request.
                        let request = Request::sign(
                            &private_key,
                            *substack.program_id(),
                            *function.name(),
                            inputs.iter(),
                            &function.input_types(),
                            rng,
                        )?;

                        // Retrieve the call stack.
                        let mut call_stack = registers.call_stack();
                        // Push the request onto the call stack.
                        call_stack.push(request.clone())?;

                        // Execute the request.
                        let response = substack.execute_function::<A, _>(call_stack, rng)?;
                        // Return the request and response.
                        (request, response)
                    }
                    // If the circuit is in evaluate mode, then throw an error.
                    CallStack::Evaluate(..) => {
                        bail!("Cannot 'execute' a function in 'evaluate' mode.")
                    }
                    // If the circuit is in execute mode, then evaluate and execute the instructions.
                    CallStack::Execute(authorization, ..) => {
                        // Retrieve the next request (without popping it).
                        let request = authorization.peek_next()?;
                        // Ensure the inputs match the original inputs.
                        request.inputs().iter().zip_eq(&inputs).try_for_each(|(request_input, input)| {
                            ensure!(request_input == input, "Inputs do not match in a 'call' instruction.");
                            Ok(())
                        })?;

                        // Evaluate the function, and load the outputs.
                        let console_response = substack.evaluate_function::<A>(registers.call_stack().replicate())?;
                        // Execute the request.
                        let response = substack.execute_function::<A, _>(registers.call_stack(), rng)?;
                        // Ensure the values are equal.
                        if console_response.outputs() != response.outputs() {
                            #[cfg(debug_assertions)]
                            eprintln!("\n{:#?} != {:#?}\n", console_response.outputs(), response.outputs());
                            bail!("Function '{}' outputs do not match in a 'call' instruction.", function.name())
                        }
                        // Return the request and response.
                        (request, response)
                    }
                }
            };
            // Inject the existing circuit.
            A::inject_r1cs(r1cs);

            use circuit::Inject;

            // Inject the network ID as `Mode::Constant`.
            let network_id = circuit::U16::constant(*request.network_id());
            // Inject the program ID as `Mode::Constant`.
            let program_id = circuit::ProgramID::constant(*substack.program_id());
            // Inject the function name as `Mode::Constant`.
            let function_name = circuit::Identifier::constant(*function.name());

            // Ensure the number of public variables remains the same.
            ensure!(A::num_public() == num_public, "Forbidden: 'call' injected excess public variables");

            // Inject the `caller` (from the request) as `Mode::Private`.
            let caller = circuit::Address::new(circuit::Mode::Private, *request.caller());
            // Inject the `sk_tag` (from the request) as `Mode::Private`.
            let sk_tag = circuit::Field::new(circuit::Mode::Private, *request.sk_tag());
            // Inject the `tvk` (from the request) as `Mode::Private`.
            let tvk = circuit::Field::new(circuit::Mode::Private, *request.tvk());
            // Inject the `tcm` (from the request) as `Mode::Private`.
            let tcm = circuit::Field::new(circuit::Mode::Private, *request.tcm());
            // Inject the input IDs (from the request) as `Mode::Public`.
            let input_ids = request
                .input_ids()
                .iter()
                .map(|input_id| circuit::InputID::new(circuit::Mode::Public, *input_id))
                .collect::<Vec<_>>();
            // Ensure the candidate input IDs match their computed inputs.
            let (check_input_ids, _) = circuit::Request::check_input_ids::<false>(
                &network_id,
                &program_id,
                &function_name,
                &input_ids,
                &inputs,
                &function.input_types(),
                &caller,
                &sk_tag,
                &tvk,
                &tcm,
                None,
            );
            A::assert(check_input_ids);

            // Inject the outputs as `Mode::Private` (with the output IDs as `Mode::Public`).
            let outputs = circuit::Response::process_outputs_from_callback(
                &network_id,
                &program_id,
                &function_name,
                num_inputs,
                &tvk,
                &tcm,
                response.outputs().to_vec(),
                &function.output_types(),
            );
            // Return the circuit outputs.
            outputs
        }
        // Else, throw an error.
        else {
            bail!("Call operator '{}' is invalid or unsupported.", call.operator())
        };

        // Assign the outputs to the destination registers.
        for (output, register) in outputs.into_iter().zip_eq(&call.destinations()) {
            // Assign the output to the register.
            registers.store_circuit(self, register, output)?;
        }

        Ok(())
    }

    /// Returns `true` if the call instruction is a function call.
    #[inline]
    pub fn is_function_call(&self, call: &Call<N>) -> Result<bool> {
        match call.operator() {
            // Check if the locator is for a function.
            CallOperator::Locator(locator) => {
                // Retrieve the program.
                let program = self.get_external_program(locator.program_id())?;
                // Check if the resource is a function.
                Ok(program.contains_function(locator.resource()))
            }
            // Check if the resource is a function.
            CallOperator::Resource(resource) => Ok(self.program().contains_function(resource)),
        }
    }

    /// Returns the output type from the given program and input types.
    #[inline]
    pub fn call_output_types(&self, call: &Call<N>, input_types: &[RegisterType<N>]) -> Result<Vec<RegisterType<N>>> {
        // Retrieve the program and resource.
        let (is_external, program, resource) = match call.operator() {
            // Retrieve the program and resource from the locator.
            CallOperator::Locator(locator) => {
                (true, self.get_external_program(locator.program_id())?, locator.resource())
            }
            CallOperator::Resource(resource) => {
                // TODO (howardwu): Revisit this decision to forbid calling internal functions. A record cannot be spent again.
                //  But there are legitimate uses for passing a record through to an internal function.
                //  We could invoke the internal function without a state transition, but need to match visibility.
                if self.program().contains_function(resource) {
                    bail!("Cannot call '{resource}'. Use a closure ('closure {resource}:') instead.")
                }

                (false, self.program(), resource)
            }
        };

        // If the operator is a closure, retrieve the closure and compute the output types.
        if let Ok(closure) = program.get_closure(resource) {
            // Ensure the number of operands matches the number of input statements.
            if closure.inputs().len() != call.operands().len() {
                bail!("Expected {} inputs, found {}", closure.inputs().len(), call.operands().len())
            }
            // Ensure the number of inputs matches the number of input statements.
            if closure.inputs().len() != input_types.len() {
                bail!("Expected {} input types, found {}", closure.inputs().len(), input_types.len())
            }
            // Ensure the number of destinations matches the number of output statements.
            if closure.outputs().len() != call.destinations().len() {
                bail!("Expected {} outputs, found {}", closure.outputs().len(), call.destinations().len())
            }
            // Return the output register types.
            Ok(closure.outputs().iter().map(|output| *output.register_type()).collect())
        }
        // If the operator is a function, retrieve the function and compute the output types.
        else if let Ok(function) = program.get_function(resource) {
            // Ensure the number of operands matches the number of input statements.
            if function.inputs().len() != call.operands().len() {
                bail!("Expected {} inputs, found {}", function.inputs().len(), call.operands().len())
            }
            // Ensure the number of inputs matches the number of input statements.
            if function.inputs().len() != input_types.len() {
                bail!("Expected {} input types, found {}", function.inputs().len(), input_types.len())
            }
            // Ensure the number of destinations matches the number of output statements.
            if function.outputs().len() != call.destinations().len() {
                bail!("Expected {} outputs, found {}", function.outputs().len(), call.destinations().len())
            }
            // Return the output register types.
            function
                .output_types()
                .into_iter()
                .map(|output_type| match (is_external, output_type) {
                    // If the output is a record and the function is external, return the external record type.
                    (true, ValueType::Record(record_name)) => Ok(RegisterType::ExternalRecord(Locator::from_str(
                        &format!("{}/{}", program.id(), record_name),
                    )?)),
                    // Else, return the register type.
                    (_, _) => Ok(RegisterType::from(output_type)),
                })
                .collect::<Result<Vec<_>>>()
        }
        // Else, throw an error.
        else {
            bail!("Call operator '{}' is invalid or unsupported.", call.operator())
        }
    }
}
