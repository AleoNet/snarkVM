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

mod helpers;
pub(crate) use helpers::*;

mod stack;
pub use stack::*;

mod trace;
use trace::*;

mod transition;
pub use transition::*;

mod add_program;

use crate::{CallOperator, Closure, Function, Instruction, Opcode, Operand, Program, ProvingKey, VerifyingKey};
use console::{
    account::PrivateKey,
    network::prelude::*,
    program::{Identifier, PlaintextType, ProgramID, Register, RegisterType, Request, Response, Value},
};

use indexmap::IndexMap;

#[allow(clippy::type_complexity)]
pub struct Process<N: Network, A: circuit::Aleo<Network = N>> {
    /// The mapping of program IDs to programs.
    programs: IndexMap<ProgramID<N>, Program<N>>,
    /// The mapping of program IDs to stacks.
    stacks: IndexMap<ProgramID<N>, Stack<N, A>>,
    /// The mapping of `(program ID, function name)` to `(proving_key, verifying_key)`.
    circuit_keys: CircuitKeys<N>,
}

impl<N: Network, A: circuit::Aleo<Network = N, BaseField = N::Field>> Process<N, A> {
    /// Initializes a new process.
    #[inline]
    pub fn new(program: Program<N>) -> Result<Self> {
        // Construct the process.
        let mut process = Self { programs: IndexMap::new(), stacks: IndexMap::new(), circuit_keys: CircuitKeys::new() };
        // Add the program to the process.
        process.add_program(&program)?;
        // Return the process.
        Ok(process)
    }

    /// Returns `true` if the process contains the program with the given ID.
    #[inline]
    pub fn contains_program(&self, program_id: &ProgramID<N>) -> bool {
        self.programs.contains_key(program_id)
    }

    /// Returns the program for the given program ID.
    #[inline]
    pub fn get_program(&self, program_id: &ProgramID<N>) -> Result<&Program<N>> {
        self.programs.get(program_id).ok_or_else(|| anyhow!("Program not found: {program_id}"))
    }

    /// Returns the stack for the given program ID.
    #[inline]
    pub fn get_stack(&self, program_id: &ProgramID<N>) -> Result<Stack<N, A>> {
        self.stacks.get(program_id).cloned().ok_or_else(|| anyhow!("Stack not found: {program_id}"))
    }

    /// Returns the proving key and verifying key for the given program ID and function name.
    #[inline]
    pub fn circuit_key(
        &self,
        program_id: &ProgramID<N>,
        function_name: &Identifier<N>,
    ) -> Result<(ProvingKey<N>, VerifyingKey<N>)> {
        // Retrieve the stack.
        let stack = self.get_stack(program_id)?;
        // Return the circuit key.
        stack.circuit_key(function_name)
    }

    /// Authorizes the request(s) to execute the program function.
    #[inline]
    pub fn authorize<R: Rng + CryptoRng>(
        &self,
        private_key: &PrivateKey<N>,
        program_id: &ProgramID<N>,
        function_name: Identifier<N>,
        inputs: &[Value<N>],
        rng: &mut R,
    ) -> Result<Authorization<N>> {
        // Retrieve the program.
        let program = self.get_program(program_id)?.clone();
        // Retrieve the function from the program.
        let function = program.get_function(&function_name)?;

        // Compute the request.
        let request = Request::sign(private_key, *program_id, function_name, inputs, &function.input_types(), rng)?;

        // Initialize the authorization.
        let authorization = Authorization::new(&[request.clone()]);

        // Prepare the stack.
        let mut stack = self.get_stack(program_id)?;
        // Execute the function.
        let (_response, _assignment) =
            stack.execute_function(CallStack::Authorize(vec![request], *private_key, authorization.clone()))?;

        // // Determine if the function contains external function calls.
        // let mut contains_external_calls = false;
        // for instruction in function.instructions() {
        //     if let Instruction::Call(call) = instruction {
        //         if let CallOperator::Locator(locator) = call.operator() {
        //             if self.get_program(locator.program_id())?.contains_function(locator.resource()) {
        //                 contains_external_calls = true;
        //                 break;
        //             }
        //         }
        //     }
        // }
        // // Construct the request builder.
        // if contains_external_calls {
        //     // // Iterate through the external calls to authorize them.
        //     // for external_call in stack.external_calls_flattened() {
        //     //     // Ensure the external program exists.
        //     //     ensure!(self.contains_program(external_call.program_id()), "External '{program_id}' not found.");
        //     //     // Retrieve the external program.
        //     //     let external_program = self.get_program(external_call.program_id())?;
        //     //     // Retrieve the external function.
        //     //     let external_function = external_program.get_function(external_call.function_name())?;
        //     //     // Retrieve the external function input types.
        //     //     let input_types = external_function.input_types();
        //     //     // Ensure the claimed input types match the function.
        //     //     ensure!(input_types == external_call.input_types(), "External call has incorrect input types.");
        //     //     // Ensure the inputs match their expected types.
        //     //     external_call
        //     //         .inputs()
        //     //         .iter()
        //     //         .zip_eq(&input_types)
        //     //         .try_for_each(|(input, input_type)| external_program.matches_value_type(input, input_type))?;
        //     //     // Authorize the request.
        //     //     let request = external_call.authorize(private_key, rng)?;
        //     //     // Append the request to the vector.
        //     //     requests.push(request);
        //     // }
        // }

        // Return the authorization.
        Ok(authorization)
    }

    /// Evaluates a program function on the given request.
    #[inline]
    pub fn evaluate(&self, request: &Request<N>) -> Result<Response<N>> {
        // Ensure the request is well-formed.
        ensure!(request.verify(), "Request is invalid");

        // Retrieve the program.
        let program = self.get_program(request.program_id())?.clone();
        // Retrieve the function from the program.
        let function = program.get_function(request.function_name())?;

        // Prepare the stack.
        let mut stack = self.get_stack(request.program_id())?;
        // Evaluate the function.
        let outputs = stack.evaluate_function(&function, request.inputs())?;
        // Compute the response.
        let response = Response::new(
            request.program_id(),
            request.inputs().len(),
            request.tvk(),
            outputs,
            &function.output_types(),
        )?;

        // Initialize the trace.
        let mut trace = Trace::<N>::new(request, &response)?;
        // Finalize the trace.
        trace.finalize()?;
        println!("{:?}", trace.leaves());

        Ok(response)
    }

    /// Executes a program function on the given request.
    #[inline]
    pub fn execute<R: Rng + CryptoRng>(
        &self,
        authorization: Authorization<N>,
        rng: &mut R,
    ) -> Result<(Response<N>, Execution<N>)> {
        trace!("Starting execute");

        // Retrieve the main request.
        let request = authorization.peek_next();
        // Ensure the request is well-formed.
        ensure!(request.verify(), "Request is invalid");
        // Prepare the stack.
        let mut stack = self.get_stack(request.program_id())?;
        // Initialize the execution.
        let execution = Execution::new();
        // Execute the circuit.
        let response = stack.execute(CallStack::Execute(authorization, execution.clone()), rng)?;

        // // Initialize the trace.
        // let mut trace = Trace::<N>::new(request, &response)?;
        // // Finalize the trace.
        // trace.finalize()?;
        // println!("{:?}", trace.leaves());

        Ok((response, execution))
    }

    /// Executes a program function on the given request, proving key, and verifying key.
    #[inline]
    pub fn execute_synthesized<R: Rng + CryptoRng>(
        &self,
        authorization: Authorization<N>,
        proving_key: &ProvingKey<N>,
        verifying_key: &VerifyingKey<N>,
        rng: &mut R,
    ) -> Result<(Response<N>, Execution<N>)> {
        trace!("Starting execute");

        // Retrieve the main request.
        let request = authorization.peek_next();
        // Ensure the request is well-formed.
        ensure!(request.verify(), "Request is invalid");
        // Add the circuit key to the mapping.
        self.circuit_keys.insert(
            request.program_id(),
            request.function_name(),
            proving_key.clone(),
            verifying_key.clone(),
        );
        // Prepare the stack.
        let mut stack = self.get_stack(request.program_id())?;
        // Initialize the execution.
        let execution = Execution::new();
        // Execute the circuit.
        let response = stack.execute(CallStack::Execute(authorization, execution.clone()), rng)?;

        // // Initialize the trace.
        // let mut trace = Trace::<N>::new(request, &response)?;
        // // Finalize the trace.
        // trace.finalize()?;
        // println!("{:?}", trace.leaves());

        Ok((response, execution))
    }

    /// Verifies a program call for the given execution.
    #[inline]
    pub fn verify(&self, execution: Execution<N>) -> Result<()> {
        trace!("Starting verify");

        // Replicate the execution stack for verification.
        let queue = Execution::new();
        for transition in execution.to_vec().into_iter() {
            queue.push(transition);
        }

        // Verify each transition.
        while let Ok(transition) = queue.pop() {
            // Ensure each input is valid.
            if transition.inputs().iter().any(|input| !input.verify()) {
                bail!("Failed to verify a transition input")
            }
            // Ensure each output is valid.
            if transition.outputs().iter().any(|output| !output.verify()) {
                bail!("Failed to verify a transition output")
            }

            // Compute the x- and y-coordinate of `tpk`.
            let (tpk_x, tpk_y) = transition.tpk().to_xy_coordinate();

            // Construct the public inputs to verify the proof.
            let mut inputs = vec![N::Field::one(), *tpk_x, *tpk_y];
            // Extend the inputs with the input IDs.
            inputs.extend(transition.input_ids().map(|id| *id));

            // Retrieve the program.
            let program = self.get_program(transition.program_id())?.clone();
            // Retrieve the function from the program.
            let function = program.get_function(transition.function_name())?;

            for instruction in function.instructions() {
                if let Instruction::Call(call) = instruction {
                    if let CallOperator::Locator(locator) = call.operator() {
                        if self.get_program(locator.program_id())?.contains_function(locator.resource()) {
                            // Peek at the next transition.
                            let transition = queue.peek_next()?;
                            // Extend the inputs with the input and output IDs of the external call.
                            inputs.extend(transition.input_ids().map(|id| *id));
                            inputs.extend(transition.output_ids().map(|id| *id));
                        }
                    }
                }
            }

            // Lastly, extend the inputs with the output IDs.
            inputs.extend(transition.output_ids().map(|id| *id));

            // Retrieve the verifying key.
            let (_, verifying_key) = self.circuit_key(transition.program_id(), transition.function_name())?;

            // Ensure the proof is valid.
            ensure!(verifying_key.verify(&inputs, &transition.proof()), "Transition is invalid");
        }
        Ok(())
    }
}

#[cfg(test)]
pub(crate) mod test_helpers {
    use super::*;
    use crate::{Process, Program};
    use console::{
        account::PrivateKey,
        network::Testnet3,
        program::{Identifier, Value},
    };

    use once_cell::sync::OnceCell;

    type CurrentNetwork = Testnet3;
    type CurrentAleo = circuit::network::AleoV0;

    pub(crate) fn sample_transition() -> Transition<CurrentNetwork> {
        static INSTANCE: OnceCell<Transition<CurrentNetwork>> = OnceCell::new();
        INSTANCE
            .get_or_init(|| {
                // Initialize a new program.
                let (string, program) = Program::<CurrentNetwork>::parse(
                    r"
program testing.aleo;

function compute:
    input r0 as u32.private;
    input r1 as u32.public;
    add r0 r1 into r2;
    output r2 as u32.public;",
                )
                .unwrap();
                assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");

                // Declare the function name.
                let function_name = Identifier::from_str("compute").unwrap();

                // Initialize the RNG.
                let rng = &mut test_crypto_rng();
                // Initialize a new caller account.
                let caller_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();

                // Construct the process.
                let process = Process::<CurrentNetwork, CurrentAleo>::new(program.clone()).unwrap();
                // Authorize the function call.
                let authorization = process
                    .authorize(
                        &caller_private_key,
                        program.id(),
                        function_name,
                        &[
                            Value::<CurrentNetwork>::from_str("5u32").unwrap(),
                            Value::<CurrentNetwork>::from_str("10u32").unwrap(),
                        ],
                        rng,
                    )
                    .unwrap();
                assert_eq!(authorization.len(), 1);
                // Execute the request.
                let (_response, execution) = process.execute(authorization, rng).unwrap();
                assert_eq!(execution.len(), 1);
                // Return the transition.
                execution.get(0).unwrap()
            })
            .clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use circuit::network::AleoV0;
    use console::{
        account::{Address, PrivateKey, ViewKey},
        network::Testnet3,
        program::{Identifier, Value},
    };

    type CurrentNetwork = Testnet3;
    type CurrentAleo = AleoV0;

    #[test]
    fn test_process_execute_call() {
        // Initialize a new program.
        let (string, program) = Program::<CurrentNetwork>::parse(
            r"
program token.aleo;

record token:
    owner as address.private;
    balance as u64.private;
    token_amount as u64.private;

// (a + (a + b)) + (a + b) == (3a + 2b)
closure execute:
    input r0 as field;
    input r1 as field;
    add r0 r1 into r2;
    add r0 r2 into r3;
    add r2 r3 into r4;
    output r4 as field;
    output r3 as field;
    output r2 as field;

function compute:
    input r0 as field.private;
    input r1 as field.public;
    input r2 as token.record;
    call execute r0 r1 into r3 r4 r5;
    output r2 as token.record;
    output r3 as field.private;
    output r4 as field.private;
    output r5 as field.private;",
        )
        .unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");

        // Declare the function name.
        let function_name = Identifier::from_str("compute").unwrap();

        // Initialize the RNG.
        let rng = &mut test_crypto_rng();

        // Initialize a new caller account.
        let caller_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let _caller_view_key = ViewKey::try_from(&caller_private_key).unwrap();
        let caller = Address::try_from(&caller_private_key).unwrap();

        // Prepare a record belonging to the address.
        let record_string =
            format!("{{ owner: {caller}.private, balance: 5u64.private, token_amount: 100u64.private }}");

        // Declare the input value.
        let r0 = Value::<CurrentNetwork>::from_str("3field").unwrap();
        let r1 = Value::<CurrentNetwork>::from_str("5field").unwrap();
        let r2 = Value::<CurrentNetwork>::from_str(&record_string).unwrap();

        // Declare the expected output value.
        let r3 = Value::from_str("19field").unwrap();
        let r4 = Value::from_str("11field").unwrap();
        let r5 = Value::from_str("8field").unwrap();

        // Construct the process.
        let process = Process::<CurrentNetwork, CurrentAleo>::new(program.clone()).unwrap();

        // Authorize the function call.
        let authorization =
            process.authorize(&caller_private_key, program.id(), function_name, &[r0, r1, r2.clone()], rng).unwrap();
        assert_eq!(authorization.len(), 1);
        let request = authorization.get(0);

        // Compute the output value.
        let response = process.evaluate(&request).unwrap();
        let candidate = response.outputs();
        assert_eq!(4, candidate.len());
        assert_eq!(r2, candidate[0]);
        assert_eq!(r3, candidate[1]);
        assert_eq!(r4, candidate[2]);
        assert_eq!(r5, candidate[3]);

        // Execute the request.
        let (response, execution) = process.execute(authorization, rng).unwrap();
        let candidate = response.outputs();
        assert_eq!(4, candidate.len());
        assert_eq!(r2, candidate[0]);
        assert_eq!(r3, candidate[1]);
        assert_eq!(r4, candidate[2]);
        assert_eq!(r5, candidate[3]);

        assert!(process.verify(execution).is_ok());

        use circuit::Environment;

        assert_eq!(37016, CurrentAleo::num_constants());
        assert_eq!(12, CurrentAleo::num_public());
        assert_eq!(41500, CurrentAleo::num_private());
        assert_eq!(41550, CurrentAleo::num_constraints());
        assert_eq!(158739, CurrentAleo::num_gates());
    }
}
