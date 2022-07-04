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

use crate::{Function, Program, ProvingKey, UniversalSRS, VerifyingKey};
use console::{
    account::{Address, PrivateKey},
    network::prelude::*,
    program::{Identifier, ProgramID, Request, Response},
};

use indexmap::IndexMap;
use parking_lot::RwLock;
use std::sync::Arc;

pub struct Process<N: Network, A: circuit::Aleo<Network = N>> {
    /// The universal SRS.
    universal_srs: Arc<UniversalSRS<N>>,
    /// The mapping of program IDs to programs.
    programs: IndexMap<ProgramID<N>, Program<N, A>>,
    /// The mapping of `(program ID, function name)` to `(proving_key, verifying_key)`.
    circuit_keys: Arc<RwLock<IndexMap<(ProgramID<N>, Identifier<N>), (ProvingKey<N>, VerifyingKey<N>)>>>,
}

impl<N: Network, A: circuit::Aleo<Network = N, BaseField = N::Field>> Process<N, A> {
    /// Initializes a new process.
    #[inline]
    pub fn new(program: Program<N, A>) -> Result<Self> {
        // TODO (howardwu): Load the universal SRS remotely.
        let universal_srs = UniversalSRS::load(100_000)?;
        // Return the process.
        Ok(Self {
            universal_srs: Arc::new(universal_srs),
            programs: [(*program.id(), program)].into_iter().collect(),
            circuit_keys: Arc::new(RwLock::new(IndexMap::new())),
        })
    }

    /// Returns the program for the given program ID.
    #[inline]
    pub fn get_program(&self, program_id: &ProgramID<N>) -> Result<&Program<N, A>> {
        self.programs.get(program_id).ok_or_else(|| anyhow!("Program not found: {program_id}"))
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
                .map(|input_type| program.sample_value(&burner_address, input_type, rng))
                .collect::<Result<Vec<_>>>()?;
            // Sign a request, with a burner private key.
            let request = program.sign(&burner_private_key, *function_name, inputs, rng)?;
            // Ensure the request is well-formed.
            ensure!(request.verify(), "Request is invalid");

            // Synthesize the circuit.
            let (_response, assignment) = Self::synthesize(program, &function, &request)?;
            // Derive the circuit key.
            let (proving_key, verifying_key) = self.universal_srs.to_circuit_key(&assignment)?;
            // Add the circuit key to the mapping.
            self.circuit_keys
                .write()
                .insert((*program_id, *function_name), (proving_key.clone(), verifying_key.clone()));
            // Return the circuit key.
            Ok((proving_key, verifying_key))
        }
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
        let mut stack = Stack::<N, A>::new(program)?;
        // Evaluate the function.
        let outputs = stack.evaluate_function(&function, request.inputs())?;
        // Compute the response.
        let response = Response::new(request.inputs().len(), request.tvk(), outputs, &function.output_types())?;

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

        // Retrieve the program.
        let program = self.get_program(request.program_id())?.clone();
        // Retrieve the function from the program.
        let function = program.get_function(request.function_name())?;

        // Retrieve the proving and verifying key.
        let (proving_key, verifying_key) = self.circuit_key(request.program_id(), request.function_name())?;
        // Synthesize the circuit.
        let (response, assignment) = Self::synthesize(program, &function, request)?;
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
}

impl<N: Network, A: circuit::Aleo<Network = N, BaseField = N::Field>> Process<N, A> {
    /// Synthesizes the given request on the specified function.
    fn synthesize(
        program: Program<N, A>,
        function: &Function<N, A>,
        request: &Request<N>,
    ) -> Result<(Response<N>, circuit::Assignment<N::Field>)> {
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
        let tpk = circuit::Group::<A>::new(circuit::Mode::Public, request.to_tpk());

        // TODO (howardwu): Check relationship to tvk.
        // Inject the request as `Mode::Private`.
        let request = circuit::Request::new(circuit::Mode::Private, request.clone());
        // Ensure the request has a valid signature and serial numbers.
        A::assert(request.verify());

        #[cfg(debug_assertions)]
        Self::log_circuit("Request Authentication");

        // Prepare the stack.
        let mut stack = Stack::<N, A>::new(program)?;
        // Execute the function.
        let outputs = stack.execute_function(function, request.inputs())?;

        #[cfg(debug_assertions)]
        Self::log_circuit(format!("Function '{}()'", function.name()));

        // Construct the response.
        let response = circuit::Response::from_outputs(num_inputs, request.tvk(), outputs, &output_types);

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
mod tests {
    use super::*;
    use circuit::network::AleoV0;
    use console::{
        account::{Address, PrivateKey, ViewKey},
        network::Testnet3,
        program::{Identifier, Plaintext, Record, Value},
    };

    type CurrentNetwork = Testnet3;
    type CurrentAleo = AleoV0;

    #[test]
    fn test_process_execute_call() {
        // Initialize a new program.
        let (string, program) = Program::<CurrentNetwork, CurrentAleo>::parse(
            r"
program token;

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

        // // Construct four inputs.
        // let input_constant = Value::Plaintext(Plaintext::from_str("{ token_amount: 9876543210u128 }").unwrap());
        // let input_public = Value::Plaintext(Plaintext::from_str("{ token_amount: 9876543210u128 }").unwrap());
        // let input_private = Value::Plaintext(Plaintext::from_str("{ token_amount: 9876543210u128 }").unwrap());
        // let input_record = Value::Record(Record::from_str(&record_string).unwrap());
        // let inputs = vec![input_constant, input_public, input_private, input_record];

        // Declare the input value.
        let r0 = Value::<CurrentNetwork>::Plaintext(Plaintext::from_str("3field").unwrap());
        let r1 = Value::<CurrentNetwork>::Plaintext(Plaintext::from_str("5field").unwrap());
        let r2 = Value::<CurrentNetwork>::Record(Record::from_str(&record_string).unwrap());

        // Declare the expected output value.
        let r3 = Value::Plaintext(Plaintext::from_str("19field").unwrap());
        let r4 = Value::Plaintext(Plaintext::from_str("11field").unwrap());
        let r5 = Value::Plaintext(Plaintext::from_str("8field").unwrap());

        // Construct the inputs and input types.
        let inputs = vec![r0, r1, r2.clone()];

        // Compute the signed request.
        let request = program.sign(&caller_private_key, function_name, inputs, rng).unwrap();

        // Construct the process.
        let process = Process::<CurrentNetwork, CurrentAleo>::new(program).unwrap();

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

        use circuit::Environment;

        assert_eq!(36664, CurrentAleo::num_constants());
        assert_eq!(12, CurrentAleo::num_public());
        assert_eq!(41650, CurrentAleo::num_private());
        assert_eq!(41700, CurrentAleo::num_constraints());
        assert_eq!(159187, CurrentAleo::num_gates());
    }
}
