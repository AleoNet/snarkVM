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

use crate::{
    process::{CallStack, Registers, RegistersCall, StackEvaluate, StackExecute},
    stack::{
        Call,
        CallOperator,
        RegistersCaller,
        RegistersCallerCircuit,
        RegistersLoad,
        RegistersLoadCircuit,
        RegistersStore,
        RegistersStoreCircuit,
        StackMatches,
        StackProgram,
    },
};
use console::{network::prelude::*, program::Request};

pub trait CallTrait<N: Network> {
    /// Evaluates the instruction.
    fn evaluate<A: circuit::Aleo<Network = N>>(
        &self,
        stack: &(impl StackEvaluate<N> + StackMatches<N> + StackProgram<N>),
        registers: &mut Registers<N, A>,
    ) -> Result<()>;

    /// Executes the instruction.
    fn execute<A: circuit::Aleo<Network = N>>(
        &self,
        stack: &(impl StackEvaluate<N> + StackExecute<N> + StackMatches<N> + StackProgram<N>),
        registers: &mut (
                 impl RegistersCall<N>
                 + RegistersCallerCircuit<N, A>
                 + RegistersLoadCircuit<N, A>
                 + RegistersStoreCircuit<N, A>
             ),
    ) -> Result<()>;
}

impl<N: Network> CallTrait<N> for Call<N> {
    /// Evaluates the instruction.
    #[inline]
    fn evaluate<A: circuit::Aleo<Network = N>>(
        &self,
        stack: &(impl StackEvaluate<N> + StackMatches<N> + StackProgram<N>),
        registers: &mut Registers<N, A>,
    ) -> Result<()> {
        // Load the operands values.
        let inputs: Vec<_> = self.operands().iter().map(|operand| registers.load(stack, operand)).try_collect()?;

        // Retrieve the substack and resource.
        let (substack, resource) = match self.operator() {
            // Retrieve the call stack and resource from the locator.
            CallOperator::Locator(locator) => {
                (stack.get_external_stack(locator.program_id())?.clone(), locator.resource())
            }
            CallOperator::Resource(resource) => {
                // TODO (howardwu): Revisit this decision to forbid calling internal functions. A record cannot be spent again.
                //  But there are legitimate uses for passing a record through to an internal function.
                //  We could invoke the internal function without a state transition, but need to match visibility.
                if stack.program().contains_function(resource) {
                    bail!("Cannot call '{resource}'. Use a closure ('closure {resource}:') instead.")
                }

                (stack.clone(), resource)
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
            bail!("Call operator '{}' is invalid or unsupported.", self.operator())
        };

        // Assign the outputs to the destination registers.
        for (output, register) in outputs.into_iter().zip_eq(&self.destinations()) {
            // Assign the output to the register.
            registers.store(stack, register, output)?;
        }

        Ok(())
    }

    /// Executes the instruction.
    #[inline]
    fn execute<A: circuit::Aleo<Network = N>>(
        &self,
        stack: &(impl StackEvaluate<N> + StackExecute<N> + StackMatches<N> + StackProgram<N>),
        registers: &mut (
                 impl RegistersCall<N>
                 + RegistersCallerCircuit<N, A>
                 + RegistersLoadCircuit<N, A>
                 + RegistersStoreCircuit<N, A>
             ),
    ) -> Result<()> {
        // Load the operands values.
        let inputs: Vec<_> =
            self.operands().iter().map(|operand| registers.load_circuit(stack, operand)).try_collect()?;

        // Retrieve the substack and resource.
        let (substack, resource) = match self.operator() {
            // Retrieve the call stack and resource from the locator.
            CallOperator::Locator(locator) => {
                // Ensure the external call is not to 'credits.aleo/fee'.
                if &locator.program_id().to_string() == "credits.aleo" && &locator.resource().to_string() == "fee" {
                    bail!("Cannot perform an external call to 'credits.aleo/fee'.")
                } else {
                    (stack.get_external_stack(locator.program_id())?.clone(), locator.resource())
                }
            }
            CallOperator::Resource(resource) => {
                // TODO (howardwu): Revisit this decision to forbid calling internal functions. A record cannot be spent again.
                //  But there are legitimate uses for passing a record through to an internal function.
                //  We could invoke the internal function without a state transition, but need to match visibility.
                if stack.program().contains_function(resource) {
                    bail!("Cannot call '{resource}'. Use a closure ('closure {resource}:') instead.")
                }

                (stack.clone(), resource)
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
                        let response = substack.execute_function::<A>(call_stack)?;

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
                        let response = substack.execute_function::<A>(call_stack)?;
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
                        let response = substack.execute_function::<A>(registers.call_stack())?;
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
            bail!("Call operator '{}' is invalid or unsupported.", self.operator())
        };

        // Assign the outputs to the destination registers.
        for (output, register) in outputs.into_iter().zip_eq(&self.destinations()) {
            // Assign the output to the register.
            registers.store_circuit(stack, register, output)?;
        }

        Ok(())
    }
}
