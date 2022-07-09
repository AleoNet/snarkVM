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

mod stack;
pub(crate) use stack::*;

mod trace;
use trace::*;

mod transition;
pub use transition::*;

mod add_program;

use crate::{
    CallOperator,
    Closure,
    Function,
    Instruction,
    Opcode,
    Operand,
    Program,
    ProvingKey,
    UniversalSRS,
    VerifyingKey,
};
use console::{
    account::{Address, PrivateKey},
    network::prelude::*,
    program::{Identifier, PlaintextType, ProgramID, Register, RegisterType, Request, Response, Value, ValueType},
};

use indexmap::IndexMap;
use once_cell::sync::OnceCell;
use parking_lot::RwLock;
use std::sync::Arc;

#[allow(clippy::type_complexity)]
pub struct Process<N: Network, A: circuit::Aleo<Network = N>> {
    /// The universal SRS.
    universal_srs: OnceCell<UniversalSRS<N>>,
    /// The mapping of program IDs to programs.
    programs: IndexMap<ProgramID<N>, Program<N>>,
    /// The mapping of program IDs to stacks.
    stacks: IndexMap<ProgramID<N>, Stack<N, A>>,
    /// The mapping of `(program ID, function name)` to `(proving_key, verifying_key)`.
    circuit_keys: Arc<RwLock<IndexMap<(ProgramID<N>, Identifier<N>), (ProvingKey<N>, VerifyingKey<N>)>>>,
}

impl<N: Network, A: circuit::Aleo<Network = N, BaseField = N::Field>> Process<N, A> {
    /// Initializes a new process.
    #[inline]
    pub fn new(program: Program<N>) -> Result<Self> {
        // Construct the process.
        let mut process = Self {
            universal_srs: OnceCell::new(),
            programs: IndexMap::new(),
            stacks: IndexMap::new(),
            circuit_keys: Arc::new(RwLock::new(IndexMap::new())),
        };
        // Add the program to the process.
        process.add_program(&program)?;
        // Return the process.
        Ok(process)
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
        // Determine if the circuit key already exists.
        let exists = self.circuit_keys.read().contains_key(&(*program_id, *function_name));
        // If the circuit key exists, retrieve and return it.
        if exists {
            // Return the circuit key.
            self.circuit_keys
                .read()
                .get(&(*program_id, *function_name))
                .cloned()
                .ok_or_else(|| anyhow!("Circuit key not found: {program_id} {function_name}"))
        }
        // If the circuit key does not exist, synthesize and return it.
        else {
            // Retrieve the program.
            let program = self.get_program(program_id)?.clone();
            // Retrieve the function from the program.
            let function = program.get_function(function_name)?;
            // Retrieve the function input types.
            let input_types = function.input_types();

            // Initialize an RNG.
            let rng = &mut rand::thread_rng();
            // Initialize a burner private key.
            let burner_private_key = PrivateKey::new(rng)?;
            // Compute the burner address.
            let burner_address = Address::try_from(&burner_private_key)?;
            // Sample the inputs.
            let inputs = input_types
                .iter()
                .map(|input_type| match input_type {
                    ValueType::ExternalRecord(locator) => {
                        // Retrieve the external program.
                        let program = self.get_program(locator.program_id())?;
                        // Sample the input.
                        program.sample_value(&burner_address, input_type, rng)
                    }
                    _ => program.sample_value(&burner_address, input_type, rng),
                })
                .collect::<Result<Vec<_>>>()?;
            // Sign a request, with a burner private key.
            let request = self.sign(&burner_private_key, program_id, *function_name, &inputs, rng)?;
            // Ensure the request is well-formed.
            ensure!(request.verify(), "Request is invalid");

            // Prepare the stack.
            let mut stack = self.get_stack(request.program_id())?;
            // Synthesize the circuit.
            let (_response, assignment) = Self::synthesize(&mut stack, &request, true)?;
            // Derive the circuit key.
            // TODO (howardwu): Load the universal SRS remotely.
            let (proving_key, verifying_key) =
                self.universal_srs.get_or_try_init(|| UniversalSRS::load(100_000))?.to_circuit_key(&assignment)?;
            // Add the circuit key to the mapping.
            self.circuit_keys
                .write()
                .insert((*program_id, *function_name), (proving_key.clone(), verifying_key.clone()));
            // Return the circuit key.
            Ok((proving_key, verifying_key))
        }
    }

    /// Signs a request to execute a program function.
    #[inline]
    pub fn sign<R: Rng + CryptoRng>(
        &self,
        private_key: &PrivateKey<N>,
        program_id: &ProgramID<N>,
        function_name: Identifier<N>,
        inputs: &[Value<N>],
        rng: &mut R,
    ) -> Result<Request<N>> {
        // Retrieve the program.
        let program = self.get_program(program_id)?.clone();
        // Retrieve the function from the program.
        let function = program.get_function(&function_name)?;
        // Compute the signed request.
        Request::sign(private_key, *program_id, function_name, inputs, &function.input_types(), rng)
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
        request: &Request<N>,
        rng: &mut R,
    ) -> Result<(Response<N>, Transition<N>)> {
        trace!("Starting execute");

        // Ensure the request is well-formed.
        ensure!(request.verify(), "Request is invalid");

        // Retrieve the proving and verifying key.
        let (proving_key, verifying_key) = self.circuit_key(request.program_id(), request.function_name())?;

        // Prepare the stack.
        let mut stack = self.get_stack(request.program_id())?;
        // Synthesize the circuit.
        let (response, assignment) = Self::synthesize(&mut stack, request, false)?;
        // Execute the circuit.
        let proof = proving_key.prove(&assignment, rng)?;
        // Verify the proof.
        ensure!(verifying_key.verify(&assignment.public_inputs(), &proof), "Proof is invalid");

        // Initialize the transition.
        let transition = Transition::from(request, &response, proof, 0u64)?;
        // Verify the transition.
        ensure!(transition.verify(&verifying_key), "Transition is invalid");

        // // Initialize the trace.
        // let mut trace = Trace::<N>::new(request, &response)?;
        // // Finalize the trace.
        // trace.finalize()?;
        // println!("{:?}", trace.leaves());

        Ok((response, transition))
    }

    /// Executes a program function on the given request, proving key, and verifying key.
    #[inline]
    pub fn execute_synthesized<R: Rng + CryptoRng>(
        &self,
        request: &Request<N>,
        proving_key: &ProvingKey<N>,
        verifying_key: &VerifyingKey<N>,
        rng: &mut R,
    ) -> Result<(Response<N>, Transition<N>)> {
        trace!("Starting execute");

        // Ensure the request is well-formed.
        ensure!(request.verify(), "Request is invalid");

        // Prepare the stack.
        let mut stack = self.get_stack(request.program_id())?;
        // Synthesize the circuit.
        let (response, assignment) = Self::synthesize(&mut stack, request, false)?;
        // Execute the circuit.
        let proof = proving_key.prove(&assignment, rng)?;
        // Verify the proof.
        ensure!(verifying_key.verify(&assignment.public_inputs(), &proof), "Proof is invalid");

        // Initialize the transition.
        let transition = Transition::from(request, &response, proof, 0u64)?;
        // Verify the transition.
        ensure!(transition.verify(verifying_key), "Transition is invalid");

        // // Initialize the trace.
        // let mut trace = Trace::<N>::new(request, &response)?;
        // // Finalize the trace.
        // trace.finalize()?;
        // println!("{:?}", trace.leaves());

        Ok((response, transition))
    }
}

impl<N: Network, A: circuit::Aleo<Network = N, BaseField = N::Field>> Process<N, A> {
    /// Synthesizes the given request on the specified function.
    fn synthesize(
        stack: &mut Stack<N, A>,
        request: &Request<N>,
        is_setup: bool,
    ) -> Result<(Response<N>, circuit::Assignment<N::Field>)> {
        // Retrieve the function from the program.
        let function = stack.program().get_function(request.function_name())?;
        // Retrieve the number of inputs.
        let num_inputs = function.inputs().len();
        // Retrieve the function output types.
        let output_types = function.output_types();

        // Ensure the number of inputs matches the number of input statements.
        if num_inputs != request.inputs().len() {
            bail!("Expected {num_inputs} inputs, found {}", request.inputs().len())
        }

        use circuit::Inject;
        // Ensure the circuit environment is clean.
        A::reset();

        // Inject the transition public key `tpk` as `Mode::Public`.
        let _tpk = circuit::Group::<A>::new(circuit::Mode::Public, request.to_tpk());

        // TODO (howardwu): Check relationship to tvk.
        // Inject the request as `Mode::Private`.
        let request = circuit::Request::new(circuit::Mode::Private, request.clone());
        // Ensure the request has a valid signature and serial numbers.
        A::assert(request.verify());

        #[cfg(debug_assertions)]
        Self::log_circuit("Request Authentication");

        // Execute the function.
        let outputs = stack.execute_function(&function, request.inputs(), is_setup)?;

        #[cfg(debug_assertions)]
        Self::log_circuit(format!("Function '{}()'", function.name()));

        // Construct the response.
        let response =
            circuit::Response::from_outputs(request.program_id(), num_inputs, request.tvk(), outputs, &output_types);

        #[cfg(debug_assertions)]
        Self::log_circuit("Response");

        // Eject the response.
        let response = circuit::Eject::eject_value(&response);
        // Finalize the circuit into an assignment.
        let assignment = A::eject_assignment_and_reset();
        // Return the response and assignment.
        Ok((response, assignment))
    }

    /// Prints the current state of the circuit.
    fn log_circuit<S: Into<String>>(scope: S) {
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
                // Compute the signed request.
                let request = process
                    .sign(
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
                // Execute the request.
                let (_response, transition) = process.execute(&request, rng).unwrap();
                // Return the transition.
                transition
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

        // Compute the signed request.
        let request =
            process.sign(&caller_private_key, program.id(), function_name, &[r0, r1, r2.clone()], rng).unwrap();

        // Compute the output value.
        let response = process.evaluate(&request).unwrap();
        let candidate = response.outputs();
        assert_eq!(4, candidate.len());
        assert_eq!(r2, candidate[0]);
        assert_eq!(r3, candidate[1]);
        assert_eq!(r4, candidate[2]);
        assert_eq!(r5, candidate[3]);

        // Execute the request.
        let (response, transition) = process.execute(&request, rng).unwrap();
        let candidate = response.outputs();
        assert_eq!(4, candidate.len());
        assert_eq!(r2, candidate[0]);
        assert_eq!(r3, candidate[1]);
        assert_eq!(r4, candidate[2]);
        assert_eq!(r5, candidate[3]);

        let (_, verifying_key) = process.circuit_key(request.program_id(), request.function_name()).unwrap();
        assert!(transition.verify(&verifying_key));

        use circuit::Environment;

        assert_eq!(37016, CurrentAleo::num_constants());
        assert_eq!(12, CurrentAleo::num_public());
        assert_eq!(41500, CurrentAleo::num_private());
        assert_eq!(41550, CurrentAleo::num_constraints());
        assert_eq!(158739, CurrentAleo::num_gates());
    }
}
