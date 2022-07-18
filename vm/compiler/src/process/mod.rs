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

mod deployment;
pub use deployment::*;

mod execution;
pub use execution::*;

mod helpers;
pub use helpers::*;

mod register_types;
pub use register_types::*;

mod registers;
pub use registers::*;

mod stack;
pub use stack::*;

mod transition;
pub use transition::*;

mod add_program;

use crate::{CallOperator, Closure, Function, Instruction, Opcode, Operand, Program, ProvingKey, VerifyingKey};
use console::{
    account::PrivateKey,
    network::prelude::*,
    program::{Identifier, PlaintextType, ProgramID, Register, RegisterType, Request, Response, Value, ValueType},
    types::I64,
};

use colored::Colorize;
use indexmap::IndexMap;
use parking_lot::RwLock;
use std::sync::Arc;

#[derive(Default)]
pub struct Process<N: Network> {
    /// The mapping of program IDs to stacks.
    stacks: IndexMap<ProgramID<N>, Stack<N>>,
    /// The mapping of `(program ID, function name)` to `(proving_key, verifying_key)`.
    circuit_keys: CircuitKeys<N>,
}

impl<N: Network> Process<N> {
    /// Initializes a new process.
    #[inline]
    pub fn new() -> Result<Self> {
        // Initialize the process.
        let process = Self { stacks: IndexMap::new(), circuit_keys: CircuitKeys::new() };
        // Return the process.
        Ok(process)
    }

    /// Returns `true` if the process contains the program with the given ID.
    #[inline]
    pub fn contains_program(&self, program_id: &ProgramID<N>) -> bool {
        self.stacks.contains_key(program_id)
    }

    /// Returns the program for the given program ID.
    #[inline]
    pub fn get_program(&self, program_id: &ProgramID<N>) -> Result<&Program<N>> {
        self.stacks
            .get(program_id)
            .map(|stack| stack.program())
            .ok_or_else(|| anyhow!("Program '{program_id}' not found"))
    }

    /// Returns the stack for the given program ID.
    #[inline]
    pub fn get_stack(&self, program_id: &ProgramID<N>) -> Result<&Stack<N>> {
        self.stacks.get(program_id).ok_or_else(|| anyhow!("Program '{program_id}' not found"))
    }

    /// Returns the proving key for the given program ID and function name.
    #[inline]
    pub fn get_proving_key(&self, program_id: &ProgramID<N>, function_name: &Identifier<N>) -> Result<ProvingKey<N>> {
        // Return the proving key.
        self.get_stack(program_id)?.get_proving_key(function_name)
    }

    /// Returns the verifying key for the given program ID and function name.
    #[inline]
    pub fn get_verifying_key(
        &self,
        program_id: &ProgramID<N>,
        function_name: &Identifier<N>,
    ) -> Result<VerifyingKey<N>> {
        // Return the verifying key.
        self.get_stack(program_id)?.get_verifying_key(function_name)
    }

    /// Inserts the given proving key, for the given program ID and function name.
    #[inline]
    pub fn insert_proving_key(
        &self,
        program_id: &ProgramID<N>,
        function_name: &Identifier<N>,
        proving_key: ProvingKey<N>,
    ) {
        // Add the proving key to the mapping.
        self.circuit_keys.insert_proving_key(program_id, function_name, proving_key);
    }

    /// Inserts the given verifying key, for the given program ID and function name.
    #[inline]
    pub fn insert_verifying_key(
        &self,
        program_id: &ProgramID<N>,
        function_name: &Identifier<N>,
        verifying_key: VerifyingKey<N>,
    ) {
        // Add the verifying key to the mapping.
        self.circuit_keys.insert_verifying_key(program_id, function_name, verifying_key);
    }

    /// Synthesizes the proving and verifying key for the given program ID and function name.
    #[inline]
    pub fn synthesize_key<A: circuit::Aleo<Network = N>, R: Rng + CryptoRng>(
        &self,
        program_id: &ProgramID<N>,
        function_name: &Identifier<N>,
        rng: &mut R,
    ) -> Result<()> {
        // Synthesize the proving and verifying key.
        self.get_stack(program_id)?.synthesize_key::<A, R>(function_name, rng)
    }

    /// Deploys the program with the given program ID, as a deployment.
    #[inline]
    pub fn deploy<A: circuit::Aleo<Network = N>, R: Rng + CryptoRng>(
        &self,
        program_id: &ProgramID<N>,
        rng: &mut R,
    ) -> Result<Deployment<N>> {
        // Compute the deployment.
        self.get_stack(program_id)?.deploy::<A, R>(rng)
    }

    /// Authorizes a call to the program function for the given inputs.
    #[inline]
    pub fn authorize<A: circuit::Aleo<Network = N>, R: Rng + CryptoRng>(
        &self,
        private_key: &PrivateKey<N>,
        program_id: &ProgramID<N>,
        function_name: Identifier<N>,
        inputs: &[Value<N>],
        rng: &mut R,
    ) -> Result<Authorization<N>> {
        // Retrieve the program, function, and input types.
        let (program, function, input_types, _) = self.get_function_info(program_id, &function_name)?;
        // Compute the request.
        let request = Request::sign(private_key, *program.id(), *function.name(), inputs, &input_types, rng)?;
        // Initialize the authorization.
        let authorization = Authorization::new(&[request.clone()]);
        // Construct the authorization from the function.
        let _response = self
            .get_stack(program.id())?
            .execute_function::<A, R>(CallStack::Authorize(vec![request], *private_key, authorization.clone()), rng)?;
        // Return the authorization.
        Ok(authorization)
    }

    /// Evaluates a program function on the given request.
    #[inline]
    pub fn evaluate<A: circuit::Aleo<Network = N>>(&self, request: &Request<N>) -> Result<Response<N>> {
        // Retrieve the program, function, and input types.
        let (program, function, input_types, output_types) =
            self.get_function_info(request.program_id(), request.function_name())?;

        // Ensure the request is well-formed.
        ensure!(request.verify(&input_types), "Request is invalid");

        // Prepare the stack.
        let stack = self.get_stack(program.id())?;
        // Evaluate the function.
        let outputs = stack.evaluate_function::<A>(&function, request.inputs())?;
        // Compute the response.
        let response = Response::new(program.id(), request.inputs().len(), request.tvk(), outputs, &output_types)?;

        Ok(response)
    }

    /// Executes the given authorization.
    #[inline]
    pub fn execute<A: circuit::Aleo<Network = N>, R: Rng + CryptoRng>(
        &self,
        authorization: Authorization<N>,
        rng: &mut R,
    ) -> Result<(Response<N>, Execution<N>)> {
        // Retrieve the main request (without popping it).
        let request = authorization.peek_next()?;
        // Prepare the stack.
        let stack = self.get_stack(request.program_id())?;

        // Ensure the network ID matches.
        ensure!(
            **request.network_id() == N::ID,
            "Network ID mismatch. Expected {}, but found {}",
            N::ID,
            request.network_id()
        );
        // Ensure that the function exists.
        if !stack.program().contains_function(request.function_name()) {
            bail!("Function '{}' does not exist.", request.function_name())
        }

        println!("{}", format!(" • Calling '{}/{}'...", request.program_id(), request.function_name()).dimmed());

        // Initialize the execution.
        let execution = Arc::new(RwLock::new(Execution::new()));
        // Execute the circuit.
        let response = stack.execute_function::<A, R>(CallStack::Execute(authorization, execution.clone()), rng)?;
        // Extract the execution.
        let execution = execution.read().clone();
        // Ensure the execution is not empty.
        ensure!(!execution.is_empty(), "Execution of '{}/{}' is empty", request.program_id(), request.function_name());

        Ok((response, execution))
    }

    /// Verifies the given deployment is well-formed.
    #[inline]
    pub fn verify_deployment<A: circuit::Aleo<Network = N>, R: Rng + CryptoRng>(
        &self,
        deployment: &Deployment<N>,
        rng: &mut R,
    ) -> Result<()> {
        // Retrieve the edition.
        let edition = deployment.edition();
        // Retrieve the program.
        let program = deployment.program().clone();
        // Retrieve the program ID.
        let program_id = deployment.program().id();

        // Ensure the edition matches.
        ensure!(edition == N::EDITION, "Deployed the wrong edition (expected '{}', found '{edition}').", N::EDITION);
        // Ensure the program does not already exist in the process.
        ensure!(!self.contains_program(program_id), "Program '{program_id}' already exists");

        // Check Program //

        // Serialize the program into bytes.
        let program_bytes = program.to_bytes_le()?;
        // Ensure the program deserializes from bytes correctly.
        ensure!(program == Program::from_bytes_le(&program_bytes)?, "Program byte serialization failed");

        // Serialize the program into string.
        let program_string = program.to_string();
        // Ensure the program deserializes from a string correctly.
        ensure!(program == Program::from_str(&program_string)?, "Program string serialization failed");

        // Ensure the program is well-formed, by computing the stack.
        let stack = self.compute_stack(&program)?;

        // Check Certificates //

        // Ensure the verifying keys are well-formed and the certificates are valid.
        stack.verify_deployment::<A, R>(deployment.verifying_keys(), rng)?;

        Ok(())
    }

    /// Verifies the given execution is valid.
    #[inline]
    pub fn verify_execution(&self, execution: &Execution<N>) -> Result<()> {
        // Retrieve the edition.
        let edition = execution.edition();
        // Ensure the edition matches.
        ensure!(edition == N::EDITION, "Executed the wrong edition (expected '{}', found '{edition}').", N::EDITION);

        // Ensure the execution contains transitions.
        ensure!(!execution.is_empty(), "There are no transitions in the execution");

        // Ensure the number of transitions matches the program function.
        {
            // Retrieve the transition (without popping it).
            let transition = execution.peek()?;
            // Retrieve the stack.
            let stack = self.get_stack(transition.program_id())?;
            // Ensure the number of calls matches the number of transitions.
            let number_of_calls = stack.get_number_of_calls(transition.function_name())?;
            ensure!(
                number_of_calls == execution.len(),
                "The number of transitions in the execution is incorrect. Expected {number_of_calls}, but found {}",
                execution.len()
            );
        }

        // Replicate the execution stack for verification.
        let mut queue = execution.clone();

        // Verify each transition.
        while let Ok(transition) = queue.pop() {
            #[cfg(debug_assertions)]
            println!("Verifying transition for {}/{}...", transition.program_id(), transition.function_name());

            // Ensure the transition ID is correct.
            ensure!(**transition.id() == transition.to_root()?, "The transition ID is incorrect");

            // Ensure the number of inputs is within the allowed range.
            ensure!(transition.inputs().len() <= N::MAX_INPUTS, "Transition exceeded maximum number of inputs");
            // Ensure the number of outputs is within the allowed range.
            ensure!(transition.outputs().len() <= N::MAX_INPUTS, "Transition exceeded maximum number of outputs");

            // Ensure each input is valid.
            if transition.inputs().iter().any(|input| !input.verify()) {
                bail!("Failed to verify a transition input")
            }
            // Ensure each output is valid.
            if transition.outputs().iter().any(|output| !output.verify()) {
                bail!("Failed to verify a transition output")
            }

            // Ensure the fee is correct.
            match Program::is_coinbase(transition.program_id(), transition.function_name()) {
                true => ensure!(transition.fee() < &0, "The fee must be negative in a coinbase transition"),
                false => ensure!(transition.fee() >= &0, "The fee must be zero or positive"),
            }

            // Compute the x- and y-coordinate of `tpk`.
            let (tpk_x, tpk_y) = transition.tpk().to_xy_coordinate();

            // Construct the public inputs to verify the proof.
            let mut inputs = vec![N::Field::one(), *tpk_x, *tpk_y];
            // Extend the inputs with the input IDs.
            inputs.extend(transition.inputs().iter().flat_map(|input| input.verifier_inputs()));

            // Retrieve the stack.
            let stack = self.get_stack(transition.program_id())?;
            // Retrieve the function from the stack.
            let function = stack.get_function(transition.function_name())?;
            // Determine the number of function calls in this function.
            let mut num_function_calls = 0;
            for instruction in function.instructions() {
                if let Instruction::Call(call) = instruction {
                    // Determine if this is a function call.
                    if call.is_function_call(stack)? {
                        num_function_calls += 1;
                    }
                }
            }
            // If there are function calls, append their inputs and outputs.
            if num_function_calls > 0 {
                // This loop takes the last `num_function_call` transitions, and reverses them
                // to order them in the order they were defined in the function.
                for transition in (*queue).iter().rev().take(num_function_calls).rev() {
                    // Extend the inputs with the input and output IDs of the external call.
                    inputs.extend(transition.input_ids().map(|id| **id));
                    inputs.extend(transition.output_ids().map(|id| **id));
                }
            }

            // Lastly, extend the inputs with the output IDs and fee.
            inputs.extend(transition.outputs().iter().flat_map(|output| output.verifier_inputs()));
            inputs.push(*I64::<N>::new(*transition.fee()).to_field()?);

            #[cfg(debug_assertions)]
            println!("Transition public inputs ({} elements): {:#?}", inputs.len(), inputs);

            // Retrieve the verifying key.
            let verifying_key = self.get_verifying_key(transition.program_id(), transition.function_name())?;
            // Ensure the proof is valid.
            ensure!(
                verifying_key.verify(transition.function_name(), &inputs, transition.proof()),
                "Transition is invalid"
            );
        }
        Ok(())
    }
}

impl<N: Network> Process<N> {
    /// Returns the program, function, and input types for the given program ID and function name.
    #[inline]
    #[allow(clippy::type_complexity)]
    fn get_function_info(
        &self,
        program_id: &ProgramID<N>,
        function_name: &Identifier<N>,
    ) -> Result<(&Program<N>, Function<N>, Vec<ValueType<N>>, Vec<ValueType<N>>)> {
        // Ensure the program exists.
        ensure!(self.contains_program(program_id), "Program '{program_id}' does not exist in the VM.");
        // Retrieve the program.
        let program = self.get_program(program_id)?;
        // Ensure the function exists.
        if !program.contains_function(function_name) {
            bail!("Function '{function_name}' does not exist in the program '{program_id}'.")
        }

        // Retrieve the function.
        let function = program.get_function(function_name)?;
        // Retrieve the input types.
        let input_types = function.input_types();
        // Retrieve the output types.
        let output_types = function.output_types();

        // Ensure the number of inputs matches the number of input types.
        if function.inputs().len() != input_types.len() {
            bail!(
                "Function '{function_name}' in the program '{program_id}' expects {} inputs, but {} types were found.",
                function.inputs().len(),
                input_types.len()
            )
        }
        // Ensure the number of outputs matches the number of output types.
        if function.outputs().len() != output_types.len() {
            bail!(
                "Function '{function_name}' in the program '{program_id}' expects {} outputs, but {} types were found.",
                function.outputs().len(),
                output_types.len()
            )
        }

        Ok((program, function, input_types, output_types))
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

    pub(crate) fn sample_key() -> (Identifier<CurrentNetwork>, ProvingKey<CurrentNetwork>, VerifyingKey<CurrentNetwork>)
    {
        static INSTANCE: OnceCell<(
            Identifier<CurrentNetwork>,
            ProvingKey<CurrentNetwork>,
            VerifyingKey<CurrentNetwork>,
        )> = OnceCell::new();
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

                // Construct the process.
                let mut process = Process::<CurrentNetwork>::new().unwrap();
                // Add the program to the process.
                process.add_program(&program).unwrap();

                // Synthesize a proving and verifying key.
                process.synthesize_key::<CurrentAleo, _>(program.id(), &function_name, rng).unwrap();

                // Get the proving and verifying key.
                let proving_key = process.get_proving_key(program.id(), &function_name).unwrap();
                let verifying_key = process.get_verifying_key(program.id(), &function_name).unwrap();

                (function_name, proving_key, verifying_key)
            })
            .clone()
    }

    pub(crate) fn sample_execution() -> Execution<CurrentNetwork> {
        static INSTANCE: OnceCell<Execution<CurrentNetwork>> = OnceCell::new();
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
                let mut process = Process::<CurrentNetwork>::new().unwrap();
                // Add the program to the process.
                process.add_program(&program).unwrap();
                // Authorize the function call.
                let authorization = process
                    .authorize::<CurrentAleo, _>(
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
                let (_response, execution) = process.execute::<CurrentAleo, _>(authorization, rng).unwrap();
                assert_eq!(execution.len(), 1);
                // Return the execution.
                execution
            })
            .clone()
    }

    pub(crate) fn sample_transition() -> Transition<CurrentNetwork> {
        // Retrieve the execution.
        let mut execution = sample_execution();
        // Ensure the execution is not empty.
        assert!(!execution.is_empty());
        // Return the transition.
        execution.pop().unwrap()
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
    fn test_process_execute_genesis() {
        // Initialize a new program.
        let program = Program::<CurrentNetwork>::genesis().unwrap();

        // Initialize the RNG.
        let rng = &mut test_crypto_rng();
        // Initialize a new caller account.
        let caller_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let _caller_view_key = ViewKey::try_from(&caller_private_key).unwrap();
        let caller = Address::try_from(&caller_private_key).unwrap();
        // Declare the input value.
        let r0 = Value::<CurrentNetwork>::from_str(&format!("{caller}")).unwrap();
        let r1 = Value::<CurrentNetwork>::from_str("1_000_000_000_000_000_u64").unwrap();
        // Declare the expected output value.
        let r2 = Value::from_str(&format!("{{ owner: {caller}.private, gates: 1_000_000_000_000_000_u64.private }}"))
            .unwrap();

        // Construct the process.
        let mut process = Process::<CurrentNetwork>::new().unwrap();
        // Add the program to the process.
        process.add_program(&program).unwrap();

        // Authorize the function call.
        let authorization = process
            .authorize::<CurrentAleo, _>(
                &caller_private_key,
                program.id(),
                Identifier::from_str("start").unwrap(),
                &[r0.clone(), r1.clone()],
                rng,
            )
            .unwrap();
        assert_eq!(authorization.len(), 1);
        let request = authorization.get(0).unwrap();
        // Compute the output value.
        let response = process.evaluate::<CurrentAleo>(&request).unwrap();
        let candidate = response.outputs();
        assert_eq!(1, candidate.len());
        assert_eq!(r2, candidate[0]);
        // Execute the request.
        let (response, execution) = process.execute::<CurrentAleo, _>(authorization, rng).unwrap();
        let candidate = response.outputs();
        assert_eq!(1, candidate.len());
        assert_eq!(r2, candidate[0]);
        assert!(process.verify_execution(&execution).is_ok());
        // use circuit::Environment;
        //
        // assert_eq!(22152, CurrentAleo::num_constants());
        // assert_eq!(9, CurrentAleo::num_public());
        // assert_eq!(20561, CurrentAleo::num_private());
        // assert_eq!(20579, CurrentAleo::num_constraints());
        // assert_eq!(79386, CurrentAleo::num_gates());

        /******************************************/

        // Ensure a non-coinbase program function fails.

        // Initialize a new program.
        let program = Program::<CurrentNetwork>::from_str(
            r"program token.aleo;

  record token:
    owner as address.private;
    gates as u64.private;

  function start:
    input r0 as address.private;
    input r1 as u64.private;
    cast r0 r1 into r2 as token.record;
    output r2 as token.record;",
        )
        .unwrap();
        process.add_program(&program).unwrap();

        let authorization = process
            .authorize::<CurrentAleo, _>(
                &caller_private_key,
                program.id(),
                Identifier::from_str("start").unwrap(),
                &[r0, r1],
                rng,
            )
            .unwrap();
        let result = process.execute::<CurrentAleo, _>(authorization, rng);
        assert!(result.is_err());
        assert_eq!(
            result.err().unwrap().to_string(),
            format!("'token.aleo/start' is not satisfied on the given inputs.")
        );
    }

    #[test]
    fn test_process_circuit_key() {
        // Initialize a new program.
        let program = Program::<CurrentNetwork>::from_str(
            r#"program testing.aleo;

function hello_world:
    input r0 as u32.public;
    input r1 as u32.private;
    add r0 r1 into r2;
    output r2 as u32.private;
"#,
        )
        .unwrap();

        // Declare the function name.
        let function_name = Identifier::from_str("hello_world").unwrap();

        // Construct the process.
        let mut process = Process::<CurrentNetwork>::new().unwrap();
        // Add the program to the process.
        process.add_program(&program).unwrap();
        // Check that the circuit key can be synthesized.
        process.synthesize_key::<CurrentAleo, _>(program.id(), &function_name, &mut test_crypto_rng()).unwrap();
    }

    #[test]
    fn test_process_multirecords() {
        // Initialize a new program.
        let program = Program::<CurrentNetwork>::from_str(
            r"program multirecord.aleo;

  record record_a:
    owner as address.private;
    gates as u64.private;

  record record_b:
    owner as address.private;
    gates as u64.private;

  function initialize:
    input r0 as record_a.record;
    input r1 as record_b.record;
    cast r0.owner r0.gates into r2 as record_a.record;
    cast r1.owner r1.gates into r3 as record_b.record;
    output r2 as record_a.record;
    output r3 as record_b.record;",
        )
        .unwrap();

        // Declare the function name.
        let function_name = Identifier::from_str("initialize").unwrap();

        // Initialize the RNG.
        let rng = &mut test_crypto_rng();

        // Initialize a new caller account.
        let caller_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let _caller_view_key = ViewKey::try_from(&caller_private_key).unwrap();
        let caller = Address::try_from(&caller_private_key).unwrap();

        // Declare the input value.
        let record_a = Value::from_str(&format!("{{ owner: {caller}.private, gates: 1234u64.private }}")).unwrap();
        let record_b = Value::from_str(&format!("{{ owner: {caller}.private, gates: 4321u64.private }}")).unwrap();

        // Construct the process.
        let mut process = Process::<CurrentNetwork>::new().unwrap();
        // Add the program to the process.
        process.add_program(&program).unwrap();

        // Authorize the function call.
        let authorization = process
            .authorize::<CurrentAleo, _>(
                &caller_private_key,
                program.id(),
                function_name,
                &[record_a.clone(), record_b.clone()],
                rng,
            )
            .unwrap();
        assert_eq!(authorization.len(), 1);
        let request = authorization.get(0).unwrap();

        // Compute the output value.
        let response = process.evaluate::<CurrentAleo>(&request).unwrap();
        let candidate = response.outputs();
        assert_eq!(2, candidate.len());
        assert_eq!(record_a, candidate[0]);
        assert_eq!(record_b, candidate[1]);

        // Execute the request.
        let (response, execution) = process.execute::<CurrentAleo, _>(authorization, rng).unwrap();
        let candidate = response.outputs();
        assert_eq!(2, candidate.len());
        assert_eq!(record_a, candidate[0]);
        assert_eq!(record_b, candidate[1]);

        assert!(process.verify_execution(&execution).is_ok());

        // use circuit::Environment;
        //
        // assert_eq!(20060, CurrentAleo::num_constants());
        // assert_eq!(12, CurrentAleo::num_public());
        // assert_eq!(57602, CurrentAleo::num_private());
        // assert_eq!(57684, CurrentAleo::num_constraints());
        // assert_eq!(178189, CurrentAleo::num_gates());
    }

    #[test]
    fn test_process_execute_call_closure() {
        // Initialize a new program.
        let (string, program) = Program::<CurrentNetwork>::parse(
            r"
program token.aleo;

record token:
    owner as address.private;
    gates as u64.private;
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
        let record_string = format!("{{ owner: {caller}.private, gates: 5u64.private, token_amount: 100u64.private }}");

        // Declare the input value.
        let r0 = Value::<CurrentNetwork>::from_str("3field").unwrap();
        let r1 = Value::<CurrentNetwork>::from_str("5field").unwrap();
        let r2 = Value::<CurrentNetwork>::from_str(&record_string).unwrap();

        // Declare the expected output value.
        let r3 = Value::from_str("19field").unwrap();
        let r4 = Value::from_str("11field").unwrap();
        let r5 = Value::from_str("8field").unwrap();

        // Construct the process.
        let mut process = Process::<CurrentNetwork>::new().unwrap();
        // Add the program to the process.
        process.add_program(&program).unwrap();
        // Check that the circuit key can be synthesized.
        process.synthesize_key::<CurrentAleo, _>(program.id(), &function_name, &mut test_crypto_rng()).unwrap();

        // Reset the process.
        let mut process = Process::<CurrentNetwork>::new().unwrap();
        // Add the program to the process.
        process.add_program(&program).unwrap();

        // Authorize the function call.
        let authorization = process
            .authorize::<CurrentAleo, _>(&caller_private_key, program.id(), function_name, &[r0, r1, r2.clone()], rng)
            .unwrap();
        assert_eq!(authorization.len(), 1);
        let request = authorization.get(0).unwrap();

        // Compute the output value.
        let response = process.evaluate::<CurrentAleo>(&request).unwrap();
        let candidate = response.outputs();
        assert_eq!(4, candidate.len());
        assert_eq!(r2, candidate[0]);
        assert_eq!(r3, candidate[1]);
        assert_eq!(r4, candidate[2]);
        assert_eq!(r5, candidate[3]);

        // Execute the request.
        let (response, execution) = process.execute::<CurrentAleo, _>(authorization, rng).unwrap();
        let candidate = response.outputs();
        assert_eq!(4, candidate.len());
        assert_eq!(r2, candidate[0]);
        assert_eq!(r3, candidate[1]);
        assert_eq!(r4, candidate[2]);
        assert_eq!(r5, candidate[3]);

        assert!(process.verify_execution(&execution).is_ok());

        // use circuit::Environment;
        //
        // assert_eq!(37080, CurrentAleo::num_constants());
        // assert_eq!(12, CurrentAleo::num_public());
        // assert_eq!(41630, CurrentAleo::num_private());
        // assert_eq!(41685, CurrentAleo::num_constraints());
        // assert_eq!(159387, CurrentAleo::num_gates());
    }

    /// TODO (howardwu): Revisit this decision. A record cannot be spent again.
    ///  But there are legitimate uses for passing a record through to an internal function.
    ///  We could invoke the internal function without a state transition, but need to match visibility.
    #[test]
    #[ignore]
    fn test_process_execute_call_internal_function() {
        // Initialize a new program.
        let (string, program) = Program::<CurrentNetwork>::parse(
            r"
program token.aleo;

record token:
    owner as address.private;
    gates as u64.private;
    amount as u64.private;

function mint:
    input r0 as address.private;
    input r1 as u64.private;
    cast r0 0u64 r1 into r2 as token.record;
    output r2 as token.record;

function transfer:
    input r0 as token.record;
    input r1 as address.private;
    input r2 as u64.private;
    sub r0.amount r2 into r3;
    call mint r1 r2 into r4; // Only for testing, this is bad practice.
    cast r0.owner r0.gates r3 into r5 as token.record;
    output r4 as token.record;
    output r5 as token.record;",
        )
        .unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");

        // Initialize the RNG.
        let rng = &mut test_crypto_rng();

        // Initialize caller 0.
        let caller0_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let caller0 = Address::try_from(&caller0_private_key).unwrap();

        // Initialize caller 1.
        let caller1_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let caller1 = Address::try_from(&caller1_private_key).unwrap();

        // Declare the function name.
        let function_name = Identifier::from_str("transfer").unwrap();

        // Declare the input value.
        let r0 = Value::<CurrentNetwork>::from_str(&format!(
            "{{ owner: {caller0}.private, gates: 5u64.private, amount: 100u64.private }}"
        ))
        .unwrap();
        let r1 = Value::<CurrentNetwork>::from_str(&caller1.to_string()).unwrap();
        let r2 = Value::<CurrentNetwork>::from_str("99u64").unwrap();

        // Declare the expected output value.
        let r4 =
            Value::from_str(&format!("{{ owner: {caller1}.private, gates: 0u64.private, amount: 99u64.private }}"))
                .unwrap();
        let r5 = Value::from_str(&format!("{{ owner: {caller0}.private, gates: 5u64.private, amount: 1u64.private }}"))
            .unwrap();

        // Construct the process.
        let mut process = Process::<CurrentNetwork>::new().unwrap();
        // Add the program to the process.
        process.add_program(&program).unwrap();

        // Authorize the function call.
        let authorization = process
            .authorize::<CurrentAleo, _>(&caller0_private_key, program.id(), function_name, &[r0, r1, r2], rng)
            .unwrap();
        assert_eq!(authorization.len(), 2);
        println!("\nAuthorize\n{:#?}\n\n", authorization.to_vec_deque());

        let mut auth_stack = authorization.to_vec_deque();

        // Compute the output value.
        let response = process.evaluate::<CurrentAleo>(&auth_stack.pop_back().unwrap()).unwrap();
        let candidate = response.outputs();
        assert_eq!(1, candidate.len());
        assert_eq!(r4, candidate[0]);

        // Compute the output value.
        let response = process.evaluate::<CurrentAleo>(&auth_stack.pop_back().unwrap()).unwrap();
        let candidate = response.outputs();
        assert_eq!(2, candidate.len());
        assert_eq!(r4, candidate[0]);
        assert_eq!(r5, candidate[1]);

        // Check again to make sure we didn't modify the authorization before calling `execute`.
        assert_eq!(authorization.len(), 2);

        // Execute the request.
        let (response, execution) = process.execute::<CurrentAleo, _>(authorization, rng).unwrap();
        let candidate = response.outputs();
        assert_eq!(2, candidate.len());
        assert_eq!(r4, candidate[0]);
        assert_eq!(r5, candidate[1]);

        assert!(process.verify_execution(&execution).is_ok());

        // use circuit::Environment;
        //
        // assert_eq!(6427, CurrentAleo::num_constants());
        // assert_eq!(8, CurrentAleo::num_public());
        // assert_eq!(21264, CurrentAleo::num_private());
        // assert_eq!(21279, CurrentAleo::num_constraints());
        // assert_eq!(81872, CurrentAleo::num_gates());
        //
        // assert_eq!(18504, CurrentAleo::num_constants());
        // assert_eq!(17, CurrentAleo::num_public());
        // assert_eq!(58791, CurrentAleo::num_private());
        // assert_eq!(58855, CurrentAleo::num_constraints());
        // assert_eq!(215810, CurrentAleo::num_gates());
    }

    #[test]
    fn test_process_execute_call_external_function() {
        // Initialize a new program.
        let (string, program0) = Program::<CurrentNetwork>::parse(
            r"
program token.aleo;

record token:
    owner as address.private;
    gates as u64.private;
    amount as u64.private;

function mint:
    input r0 as address.private;
    input r1 as u64.private;
    cast r0 0u64 r1 into r2 as token.record;
    output r2 as token.record;

function transfer:
    input r0 as token.record;
    input r1 as address.private;
    input r2 as u64.private;
    sub r0.amount r2 into r3;
    cast r1 0u64 r2 into r4 as token.record;
    cast r0.owner r0.gates r3 into r5 as token.record;
    output r4 as token.record;
    output r5 as token.record;",
        )
        .unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");

        // Construct the process.
        let mut process = Process::<CurrentNetwork>::new().unwrap();
        // Add the program to the process.
        process.add_program(&program0).unwrap();

        // Initialize another program.
        let (string, program1) = Program::<CurrentNetwork>::parse(
            r"
import token.aleo;

program wallet.aleo;

function transfer:
    input r0 as token.aleo/token.record;
    input r1 as address.private;
    input r2 as u64.private;
    call token.aleo/transfer r0 r1 r2 into r3 r4;
    output r3 as token.aleo/token.record;
    output r4 as token.aleo/token.record;",
        )
        .unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");

        // Add the program to the process.
        process.add_program(&program1).unwrap();

        // Initialize the RNG.
        let rng = &mut test_crypto_rng();

        // Initialize caller 0.
        let caller0_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let caller0 = Address::try_from(&caller0_private_key).unwrap();

        // Initialize caller 1.
        let caller1_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let caller1 = Address::try_from(&caller1_private_key).unwrap();

        // Declare the function name.
        let function_name = Identifier::from_str("transfer").unwrap();

        // Declare the input value.
        let r0 = Value::<CurrentNetwork>::from_str(&format!(
            "{{ owner: {caller0}.private, gates: 0u64.private, amount: 100u64.private }}"
        ))
        .unwrap();
        let r1 = Value::<CurrentNetwork>::from_str(&caller1.to_string()).unwrap();
        let r2 = Value::<CurrentNetwork>::from_str("99u64").unwrap();

        // Declare the expected output value.
        let r4 =
            Value::from_str(&format!("{{ owner: {caller1}.private, gates: 0u64.private, amount: 99u64.private }}"))
                .unwrap();
        let r5 = Value::from_str(&format!("{{ owner: {caller0}.private, gates: 0u64.private, amount: 1u64.private }}"))
            .unwrap();

        // Authorize the function call.
        let authorization = process
            .authorize::<CurrentAleo, _>(&caller0_private_key, program1.id(), function_name, &[r0, r1, r2], rng)
            .unwrap();
        assert_eq!(authorization.len(), 2);
        println!("\nAuthorize\n{:#?}\n\n", authorization.to_vec_deque());

        let mut auth_stack = authorization.to_vec_deque();

        // // Compute the output value.
        // let response = process.evaluate::<CurrentAleo>(&auth_stack.pop_back().unwrap()).unwrap();
        // let candidate = response.outputs();
        // assert_eq!(1, candidate.len());
        // assert_eq!(r5, candidate[0]);
        //
        // // Compute the output value.
        // let response = process.evaluate::<CurrentAleo>(&auth_stack.pop_back().unwrap()).unwrap();
        // let candidate = response.outputs();
        // assert_eq!(1, candidate.len());
        // assert_eq!(r4, candidate[0]);

        // Compute the output value.
        let response = process.evaluate::<CurrentAleo>(&auth_stack.pop_back().unwrap()).unwrap();
        let candidate = response.outputs();
        assert_eq!(2, candidate.len());
        assert_eq!(r4, candidate[0]);
        assert_eq!(r5, candidate[1]);

        // Compute the output value.
        let response = process.evaluate::<CurrentAleo>(&auth_stack.pop_back().unwrap()).unwrap();
        let candidate = response.outputs();
        assert_eq!(2, candidate.len());
        assert_eq!(r4, candidate[0]);
        assert_eq!(r5, candidate[1]);

        // Check again to make sure we didn't modify the authorization before calling `execute`.
        assert_eq!(authorization.len(), 2);

        // Execute the request.
        let (response, execution) = process.execute::<CurrentAleo, _>(authorization, rng).unwrap();
        let candidate = response.outputs();
        assert_eq!(2, candidate.len());
        assert_eq!(r4, candidate[0]);
        assert_eq!(r5, candidate[1]);

        assert!(process.verify_execution(&execution).is_ok());

        // use circuit::Environment;
        //
        // assert_eq!(6427, CurrentAleo::num_constants());
        // assert_eq!(8, CurrentAleo::num_public());
        // assert_eq!(21264, CurrentAleo::num_private());
        // assert_eq!(21279, CurrentAleo::num_constraints());
        // assert_eq!(81872, CurrentAleo::num_gates());
        //
        // assert_eq!(18504, CurrentAleo::num_constants());
        // assert_eq!(17, CurrentAleo::num_public());
        // assert_eq!(58791, CurrentAleo::num_private());
        // assert_eq!(58855, CurrentAleo::num_constraints());
        // assert_eq!(215810, CurrentAleo::num_gates());
    }
}
