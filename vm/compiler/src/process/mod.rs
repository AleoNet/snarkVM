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
    types::I64,
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

    /// Inserts the given proving key and verifying key, for the given program ID and function name.
    #[inline]
    pub fn insert_circuit_key(
        &self,
        program_id: &ProgramID<N>,
        function_name: &Identifier<N>,
        proving_key: ProvingKey<N>,
        verifying_key: VerifyingKey<N>,
    ) {
        // Add the circuit key to the mapping.
        self.circuit_keys.insert(program_id, function_name, proving_key, verifying_key);
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
        // Construct the authorization from the function.
        let (_response, _assignment) =
            stack.execute_function(CallStack::Authorize(vec![request], *private_key, authorization.clone()))?;

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

        // Retrieve the main request (without popping it).
        let request = authorization.peek_next()?;
        // Prepare the stack.
        let mut stack = self.get_stack(request.program_id())?;

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

        // Ensure the request is well-formed.
        ensure!(request.verify(), "Request is invalid");

        // Initialize the execution.
        let execution = Execution::new();
        // Execute the circuit.
        let response = stack.execute(CallStack::Execute(authorization, execution.clone()), rng)?;

        Ok((response, execution))
    }

    /// Verifies a program call for the given execution.
    #[inline]
    pub fn verify(&self, execution: Execution<N>) -> Result<()> {
        trace!("Starting verify");

        // Ensure the execution contains transitions.
        ensure!(!execution.is_empty(), "There are no transitions in the execution");

        // Replicate the execution stack for verification.
        let queue = Execution::from(&execution.to_vec());

        // Verify each transition.
        while let Ok(transition) = queue.pop() {
            #[cfg(debug_assertions)]
            println!("Verifying transition for {}/{}...", transition.program_id(), transition.function_name());

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
            // Determine the number of function calls in this function.
            let mut num_function_calls = 0;
            for instruction in function.instructions() {
                if let Instruction::Call(call) = instruction {
                    // Retrieve the program and resource.
                    let (program, resource) = match call.operator() {
                        CallOperator::Locator(locator) => (self.get_program(locator.program_id())?, locator.resource()),
                        CallOperator::Resource(resource) => (&program, resource),
                    };
                    if program.contains_function(resource) {
                        num_function_calls += 1;
                    }
                }
            }
            // If there are function calls, append their inputs and outputs.
            if num_function_calls > 0 {
                // This loop takes the last `num_function_call` transitions, and reverses them
                // to order them in the order they were defined in the function.
                for transition in queue.to_vec().iter().rev().take(num_function_calls).rev() {
                    // Extend the inputs with the input and output IDs of the external call.
                    inputs.extend(transition.input_ids().map(|id| *id));
                    inputs.extend(transition.output_ids().map(|id| *id));
                }
            }

            // Lastly, extend the inputs with the output IDs and fee.
            inputs.extend(transition.output_ids().map(|id| *id));
            inputs.push(*I64::<N>::new(*transition.fee()).to_field()?);

            // Retrieve the verifying key.
            let (_, verifying_key) = self.circuit_key(transition.program_id(), transition.function_name())?;

            #[cfg(debug_assertions)]
            println!("Transition public inputs ({} elements): {:#?}", inputs.len(), inputs);

            // Ensure the proof is valid.
            ensure!(verifying_key.verify(&inputs, transition.proof()), "Transition is invalid");
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
    fn test_process_execute_genesis() {
        // Initialize a new program.
        let program = Program::<CurrentNetwork>::from_str(
            r"program stake.aleo;

  record stake:
    owner as address.private;
    balance as u64.private;

  function initialize:
    input r0 as address.private;
    input r1 as u64.private;
    cast r0 r1 into r2 as stake.record;
    output r2 as stake.record;",
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
        let r0 = Value::<CurrentNetwork>::from_str(&format!("{caller}")).unwrap();
        let r1 = Value::<CurrentNetwork>::from_str("1_000_000_000_000_000_u64").unwrap();

        // Declare the expected output value.
        let r2 = Value::from_str(&format!("{{ owner: {caller}.private, balance: 1_000_000_000_000_000_u64.private }}"))
            .unwrap();

        // Construct the process.
        let mut process = Process::<CurrentNetwork, CurrentAleo>::new(program.clone()).unwrap();

        // Authorize the function call.
        let authorization = process
            .authorize(&caller_private_key, program.id(), function_name, &[r0.clone(), r1.clone()], rng)
            .unwrap();
        assert_eq!(authorization.len(), 1);
        let request = authorization.get(0).unwrap();

        // Compute the output value.
        let response = process.evaluate(&request).unwrap();
        let candidate = response.outputs();
        assert_eq!(1, candidate.len());
        assert_eq!(r2, candidate[0]);

        // Execute the request.
        let (response, execution) = process.execute(authorization, rng).unwrap();
        let candidate = response.outputs();
        assert_eq!(1, candidate.len());
        assert_eq!(r2, candidate[0]);

        assert!(process.verify(execution).is_ok());

        // use circuit::Environment;
        //
        // assert_eq!(22152, CurrentAleo::num_constants());
        // assert_eq!(9, CurrentAleo::num_public());
        // assert_eq!(20561, CurrentAleo::num_private());
        // assert_eq!(20579, CurrentAleo::num_constraints());
        // assert_eq!(79386, CurrentAleo::num_gates());

        /******************************************/

        // Ensure a non-special program fails.

        // Initialize a new program.
        let program = Program::<CurrentNetwork>::from_str(
            r"program token.aleo;

  record token:
    owner as address.private;
    balance as u64.private;

  function initialize:
    input r0 as address.private;
    input r1 as u64.private;
    cast r0 r1 into r2 as token.record;
    output r2 as token.record;",
        )
        .unwrap();

        process.add_program(&program).unwrap();

        let authorization =
            process.authorize(&caller_private_key, program.id(), function_name, &[r0, r1], rng).unwrap();
        let result = process.execute(authorization, rng);
        assert!(result.is_err());
        assert_eq!(
            result.err().unwrap().to_string(),
            format!("The circuit for 'token.aleo/initialize' is not satisfied with the given inputs.")
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
        let process = Process::<CurrentNetwork, CurrentAleo>::new(program.clone()).unwrap();
        // Check that the circuit key can be synthesized.
        process.circuit_key(program.id(), &function_name).unwrap();
    }

    #[test]
    fn test_process_execute_call_closure() {
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
        // Check that the circuit key can be synthesized.
        process.circuit_key(program.id(), &function_name).unwrap();

        // Reset the process.
        let process = Process::<CurrentNetwork, CurrentAleo>::new(program.clone()).unwrap();

        // Authorize the function call.
        let authorization =
            process.authorize(&caller_private_key, program.id(), function_name, &[r0, r1, r2.clone()], rng).unwrap();
        assert_eq!(authorization.len(), 1);
        let request = authorization.get(0).unwrap();

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

        // use circuit::Environment;
        //
        // assert_eq!(37080, CurrentAleo::num_constants());
        // assert_eq!(12, CurrentAleo::num_public());
        // assert_eq!(41630, CurrentAleo::num_private());
        // assert_eq!(41685, CurrentAleo::num_constraints());
        // assert_eq!(159387, CurrentAleo::num_gates());
    }

    #[test]
    fn test_process_execute_call_internal_function() {
        // Initialize a new program.
        let (string, program) = Program::<CurrentNetwork>::parse(
            r"
program token.aleo;

record token:
    owner as address.private;
    balance as u64.private;
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
    cast r0.owner r0.balance r3 into r5 as token.record;
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
            "{{ owner: {caller0}.private, balance: 5u64.private, amount: 100u64.private }}"
        ))
        .unwrap();
        let r1 = Value::<CurrentNetwork>::from_str(&caller1.to_string()).unwrap();
        let r2 = Value::<CurrentNetwork>::from_str("99u64").unwrap();

        // Declare the expected output value.
        let r4 =
            Value::from_str(&format!("{{ owner: {caller1}.private, balance: 0u64.private, amount: 99u64.private }}"))
                .unwrap();
        let r5 =
            Value::from_str(&format!("{{ owner: {caller0}.private, balance: 5u64.private, amount: 1u64.private }}"))
                .unwrap();

        // Construct the process.
        let process = Process::<CurrentNetwork, CurrentAleo>::new(program.clone()).unwrap();

        // Authorize the function call.
        let authorization =
            process.authorize(&caller0_private_key, program.id(), function_name, &[r0, r1, r2], rng).unwrap();
        assert_eq!(authorization.len(), 2);
        println!("\nAuthorize\n{:#?}\n\n", authorization.to_vec_deque());

        let mut auth_stack = authorization.to_vec_deque();

        // Compute the output value.
        let response = process.evaluate(&auth_stack.pop_back().unwrap()).unwrap();
        let candidate = response.outputs();
        assert_eq!(1, candidate.len());
        assert_eq!(r4, candidate[0]);

        // Compute the output value.
        let response = process.evaluate(&auth_stack.pop_back().unwrap()).unwrap();
        let candidate = response.outputs();
        assert_eq!(2, candidate.len());
        assert_eq!(r4, candidate[0]);
        assert_eq!(r5, candidate[1]);

        // Check again to make sure we didn't modify the authorization before calling `execute`.
        assert_eq!(authorization.len(), 2);

        // Execute the request.
        let (response, execution) = process.execute(authorization, rng).unwrap();
        let candidate = response.outputs();
        assert_eq!(2, candidate.len());
        assert_eq!(r4, candidate[0]);
        assert_eq!(r5, candidate[1]);

        assert!(process.verify(execution).is_ok());

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
    balance as u64.private;
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
    call mint r0.owner r3 into r5; // Only for testing, this is bad practice.
    output r4 as token.record;
    output r5 as token.record;",
        )
        .unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");

        // Construct the process.
        let mut process = Process::<CurrentNetwork, CurrentAleo>::new(program0).unwrap();

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
            "{{ owner: {caller0}.private, balance: 0u64.private, amount: 100u64.private }}"
        ))
        .unwrap();
        let r1 = Value::<CurrentNetwork>::from_str(&caller1.to_string()).unwrap();
        let r2 = Value::<CurrentNetwork>::from_str("99u64").unwrap();

        // Declare the expected output value.
        let r4 =
            Value::from_str(&format!("{{ owner: {caller1}.private, balance: 0u64.private, amount: 99u64.private }}"))
                .unwrap();
        let r5 =
            Value::from_str(&format!("{{ owner: {caller0}.private, balance: 0u64.private, amount: 1u64.private }}"))
                .unwrap();

        // Authorize the function call.
        let authorization =
            process.authorize(&caller0_private_key, program1.id(), function_name, &[r0, r1, r2], rng).unwrap();
        assert_eq!(authorization.len(), 4);
        println!("\nAuthorize\n{:#?}\n\n", authorization.to_vec_deque());

        let mut auth_stack = authorization.to_vec_deque();

        // Compute the output value.
        let response = process.evaluate(&auth_stack.pop_back().unwrap()).unwrap();
        let candidate = response.outputs();
        assert_eq!(1, candidate.len());
        assert_eq!(r5, candidate[0]);

        // Compute the output value.
        let response = process.evaluate(&auth_stack.pop_back().unwrap()).unwrap();
        let candidate = response.outputs();
        assert_eq!(1, candidate.len());
        assert_eq!(r4, candidate[0]);

        // Compute the output value.
        let response = process.evaluate(&auth_stack.pop_back().unwrap()).unwrap();
        let candidate = response.outputs();
        assert_eq!(2, candidate.len());
        assert_eq!(r4, candidate[0]);
        assert_eq!(r5, candidate[1]);

        // Compute the output value.
        let response = process.evaluate(&auth_stack.pop_back().unwrap()).unwrap();
        let candidate = response.outputs();
        assert_eq!(2, candidate.len());
        assert_eq!(r4, candidate[0]);
        assert_eq!(r5, candidate[1]);

        // Check again to make sure we didn't modify the authorization before calling `execute`.
        assert_eq!(authorization.len(), 4);

        // Execute the request.
        let (response, execution) = process.execute(authorization, rng).unwrap();
        let candidate = response.outputs();
        assert_eq!(2, candidate.len());
        assert_eq!(r4, candidate[0]);
        assert_eq!(r5, candidate[1]);

        assert!(process.verify(execution).is_ok());

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
