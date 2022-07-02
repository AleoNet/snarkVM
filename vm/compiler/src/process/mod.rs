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

mod trace;
use trace::*;

use crate::{Program, Stack};
use console::{
    network::prelude::*,
    program::{Call, InputID, Plaintext, StackValue, Value, ValueType},
};

pub struct Process<N: Network, A: circuit::Aleo<Network = N>> {
    /// The program (record types, interfaces, functions).
    program: Program<N, A>,
}

impl<N: Network, A: circuit::Aleo<Network = N>> Process<N, A> {
    /// Evaluates a program function on the given inputs.
    #[inline]
    pub fn evaluate(&self, call: &Call<N>) -> Result<Vec<Value<N, Plaintext<N>>>> {
        // Ensure the call is well-formed.
        ensure!(call.verify(), "Call is invalid");

        // Retrieve the inputs.
        let inputs = call.inputs();
        // Retrieve the number of inputs.
        let num_inputs = inputs.len();
        // Retrieve the function from the program.
        let function = self.program.get_function(call.function_name())?;
        // Ensure the number of inputs matches the number of input statements.
        if function.inputs().len() != num_inputs {
            bail!("Expected {} inputs, found {num_inputs}", function.inputs().len())
        }

        // Initialize the trace.
        let mut trace = Trace::<N>::new(*call.caller())?;

        // Prepare the inputs.
        call.input_ids().iter().try_for_each(|input_id| {
            match input_id {
                // A constant input is hashed to a field element.
                InputID::Constant(input_hash) => trace.add_input(*input_hash),
                // A public input is hashed to a field element.
                InputID::Public(input_hash) => trace.add_input(*input_hash),
                // A private input is committed (using `tvk`) to a field element.
                InputID::Private(_, commitment) => trace.add_input(*commitment),
                // An input record is computed to its serial number.
                InputID::Record(_, _, _, _, serial_number) => trace.add_input(*serial_number),
            }
        })?;

        // Prepare the stack.
        let mut stack = Stack::<N, A>::new(Some(self.program.clone()))?;
        // Evaluate the function.
        let outputs = stack.evaluate_function(&function, &inputs)?;

        // Load the outputs.
        outputs.iter().enumerate().try_for_each(|(index, output)| {
            match output {
                // For a constant output, compute the hash of the output.
                Value::Constant(output) => {
                    // Hash the output to a field element.
                    let output_hash = N::hash_bhp1024(&output.to_bits_le())?;
                    // Add the output hash to the trace.
                    trace.add_output(output_hash)?;
                }
                // For a public output, compute the hash of the output.
                Value::Public(output) => {
                    // Hash the output to a field element.
                    let output_hash = N::hash_bhp1024(&output.to_bits_le())?;
                    // Add the output hash to the trace.
                    trace.add_output(output_hash)?;
                }
                // For a private output, compute the commitment (using `tvk`) for the output.
                Value::Private(output) => {
                    // Construct the (console) output index as a field element.
                    let index = console::types::Field::from_u16((num_inputs + index) as u16);
                    // Compute the commitment randomizer as `HashToScalar(tvk || index)`.
                    let randomizer = N::hash_to_scalar_psd2(&[*call.tvk(), index])?;
                    // Commit the output to a field element.
                    let commitment = N::commit_bhp1024(&output.to_bits_le(), &randomizer)?;
                    // Add the output commitment to the trace.
                    trace.add_output(commitment)?;
                }
                // For an output record, compute the record commitment, and encrypt the record (using `tvk`).
                // An expected record commitment is injected as `Mode::Public`, and compared to the computed record commitment.
                Value::Record(record) => {
                    // Compute the record commitment.
                    let commitment = record.to_commitment()?;
                    // Add the record commitment to the trace.
                    trace.add_output(commitment)?;

                    // Construct the (console) output index as a field element.
                    let index = console::types::Field::from_u16((num_inputs + index) as u16);
                    // Compute the encryption randomizer as `HashToScalar(tvk || index)`.
                    let randomizer = N::hash_to_scalar_psd2(&[*call.tvk(), index])?;

                    // Compute the record nonce.
                    let nonce = N::g_scalar_multiply(&randomizer).to_x_coordinate();

                    // Encrypt the record, using the randomizer.
                    let encrypted_record = record.encrypt(randomizer)?;
                    // Compute the record checksum, as the hash of the encrypted record.
                    let checksum = N::hash_bhp1024(&encrypted_record.to_bits_le())?;
                }
            };

            Ok::<_, Error>(())
        })?;

        // Finalize the trace.
        trace.finalize()?;

        println!("{:?}", trace.leaves());

        Ok(outputs)
    }

    /// Executes a program function on the given inputs.
    #[inline]
    pub fn execute(&self, call: &Call<N>) -> Result<Vec<circuit::Value<A, circuit::Plaintext<A>>>> {
        // Ensure the call is well-formed.
        ensure!(call.verify(), "Call is invalid");

        // Retrieve the inputs.
        let inputs = call.inputs();
        // Retrieve the number of inputs.
        let num_inputs = inputs.len();
        // Retrieve the function from the program.
        let function = self.program.get_function(call.function_name())?;
        // Ensure the number of inputs matches the number of input statements.
        if function.inputs().len() != num_inputs {
            bail!("Expected {} inputs, found {num_inputs}", function.inputs().len())
        }

        // Initialize the trace.
        let mut trace = Trace::<N>::new(*call.caller())?;

        // Prepare the inputs.
        call.input_ids().iter().try_for_each(|input_id| {
            match input_id {
                // A constant input is hashed to a field element.
                InputID::Constant(input_hash) => trace.add_input(*input_hash),
                // A public input is hashed to a field element.
                InputID::Public(input_hash) => trace.add_input(*input_hash),
                // A private input is committed (using `tvk`) to a field element.
                InputID::Private(_, commitment) => trace.add_input(*commitment),
                // An input record is computed to its serial number.
                InputID::Record(_, _, _, _, serial_number) => trace.add_input(*serial_number),
            }
        })?;

        // Ensure the circuit environment is clean.
        A::reset();

        use circuit::Inject;

        // Inject the transition view key `tvk` as `Mode::Public`.
        let tvk = circuit::Field::<A>::new(circuit::Mode::Public, call.tvk().clone());
        // Inject the call as `Mode::Private`.
        let call = circuit::Call::new(circuit::Mode::Private, call.clone());
        // Ensure the `tvk` matches.
        A::assert_eq(call.tvk(), tvk);
        // Ensure the call has a valid signature and serial numbers.
        A::assert(call.verify());

        #[cfg(debug_assertions)]
        Self::log_circuit("Call Authentication");

        // Prepare the stack.
        let mut stack = Stack::<N, A>::new(Some(self.program.clone()))?;
        // Execute the function.
        let outputs = stack.execute_function(&function, call.inputs())?;

        #[cfg(debug_assertions)]
        Self::log_circuit(format!("Function {}", function.name()));

        // Load the outputs.
        outputs.iter().enumerate().try_for_each(|(index, output)| {
            use circuit::{Eject, ToBits};

            match output {
                // For a constant output, compute the hash of the output.
                // An expected hash is injected as `Mode::Constant`, and compared to the computed hash.
                circuit::Value::Constant(output) => {
                    // Hash the output to a field element.
                    let output_hash = A::hash_bhp1024(&output.to_bits_le());
                    // Inject the expected hash as `Mode::Public`.
                    let expected_hash = circuit::Field::<A>::new(circuit::Mode::Constant, output_hash.eject_value());
                    // Ensure the computed hash matches the expected hash.
                    A::assert_eq(&output_hash, expected_hash);

                    #[cfg(debug_assertions)]
                    Self::log_circuit("Constant Output");

                    // Add the output hash to the trace.
                    trace.add_output(output_hash.eject_value())?;
                }
                // For a public output, compute the hash of the output.
                // An expected hash is injected as `Mode::Public`, and compared to the computed hash.
                circuit::Value::Public(output) => {
                    // Hash the output to a field element.
                    let output_hash = A::hash_bhp1024(&output.to_bits_le());
                    // Inject the expected hash as `Mode::Public`.
                    let expected_hash = circuit::Field::<A>::new(circuit::Mode::Public, output_hash.eject_value());
                    // Ensure the computed hash matches the expected hash.
                    A::assert_eq(&output_hash, expected_hash);

                    #[cfg(debug_assertions)]
                    Self::log_circuit("Public Output");

                    // Add the output hash to the trace.
                    trace.add_output(output_hash.eject_value())?;
                }
                // For a private output, compute the commitment (using `tvk`) for the output.
                // An expected commitment is injected as `Mode::Public`, and compared to the commitment.
                circuit::Value::Private(output) => {
                    // Construct the (console) output index as a field element.
                    let index = console::types::Field::from_u16((num_inputs + index) as u16);
                    // Inject the output index as `Mode::Private`.
                    let output_index = circuit::Field::new(circuit::Mode::Private, index);
                    // Compute the commitment randomizer as `HashToScalar(tvk || index)`.
                    let randomizer = A::hash_to_scalar_psd2(&[call.tvk().clone(), output_index]);

                    // Commit the output to a field element.
                    let commitment = A::commit_bhp1024(&output.to_bits_le(), &randomizer);
                    // Inject the expected commitment as `Mode::Public`.
                    let expected_cm = circuit::Field::<A>::new(circuit::Mode::Public, commitment.eject_value());
                    // Ensure the computed commitment matches the expected commitment.
                    A::assert_eq(&commitment, expected_cm);

                    #[cfg(debug_assertions)]
                    Self::log_circuit("Private Output");

                    // Add the output commitment to the trace.
                    trace.add_output(commitment.eject_value())?;
                }
                // For an output record, compute the record commitment, and encrypt the record (using `tvk`).
                // An expected record commitment is injected as `Mode::Public`, and compared to the computed record commitment.
                circuit::Value::Record(record) => {
                    // Compute the record commitment.
                    let commitment = record.to_commitment();
                    // Inject the expected record commitment as `Mode::Public`.
                    let expected_cm = circuit::Field::<A>::new(circuit::Mode::Public, commitment.eject_value());
                    // Ensure the computed record commitment matches the expected record commitment.
                    A::assert_eq(&commitment, expected_cm);

                    // Add the record commitment to the trace.
                    trace.add_output(commitment.eject_value())?;

                    // Construct the (console) output index as a field element.
                    let index = console::types::Field::from_u16((num_inputs + index) as u16);
                    // Inject the output index as `Mode::Private`.
                    let output_index = circuit::Field::new(circuit::Mode::Private, index);
                    // Compute the encryption randomizer as `HashToScalar(tvk || index)`.
                    let randomizer = A::hash_to_scalar_psd2(&[call.tvk().clone(), output_index]);

                    // Compute the record nonce.
                    let nonce = A::g_scalar_multiply(&randomizer).to_x_coordinate();
                    // Inject the expected nonce as `Mode::Public`.
                    let expected_nonce = circuit::Field::<A>::new(circuit::Mode::Public, nonce.eject_value());
                    // Ensure the computed nonce matches the expected nonce.
                    A::assert_eq(&nonce, expected_nonce);

                    // Encrypt the record, using the randomizer.
                    let encrypted_record = record.encrypt(&randomizer);
                    // Compute the record checksum, as the hash of the encrypted record.
                    let checksum = A::hash_bhp1024(&encrypted_record.to_bits_le());
                    // Inject the expected record checksum as `Mode::Public`.
                    let expected_checksum = circuit::Field::<A>::new(circuit::Mode::Public, checksum.eject_value());
                    // Ensure the computed record checksum matches the expected record checksum.
                    A::assert_eq(&checksum, expected_checksum);

                    #[cfg(debug_assertions)]
                    Self::log_circuit("Record Output");
                }
            };

            Ok::<_, Error>(())
        })?;

        // Finalize the trace.
        trace.finalize()?;

        println!("{:?}", trace.leaves());

        Ok(outputs)
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
        account::{Address, ComputeKey, PrivateKey, ViewKey},
        network::Testnet3,
        program::{Identifier, ProgramID, Record, Request},
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

        // Declare the input value.
        let r0 = StackValue::<CurrentNetwork>::Plaintext(Plaintext::from_str("3field").unwrap());
        let r1 = StackValue::<CurrentNetwork>::Plaintext(Plaintext::from_str("5field").unwrap());
        let r2 =
            StackValue::<CurrentNetwork>::Record(Record::from_str("{ owner: aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.private, balance: 5u64.private, token_amount: 100u64.private }").unwrap());

        // Declare the expected output value.
        let r3 = Value::Private(Plaintext::from_str("19field").unwrap());
        let r4 = Value::Private(Plaintext::from_str("11field").unwrap());
        let r5 = Value::Private(Plaintext::from_str("8field").unwrap());

        // Initialize the RNG.
        let rng = &mut test_crypto_rng();

        // Initialize a new caller account.
        let caller_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let caller_compute_key = ComputeKey::try_from(&caller_private_key).unwrap();
        let _caller_view_key = ViewKey::try_from(&caller_private_key).unwrap();
        let caller = Address::try_from(&caller_private_key).unwrap();

        // Construct the inputs and input types.
        let inputs = vec![r0, r1, r2];
        let input_types = vec![
            ValueType::from_str("field.private").unwrap(),
            ValueType::from_str("field.public").unwrap(),
            ValueType::from_str("token.record").unwrap(),
        ];

        // Construct the call via a request.
        let call = Request::new(caller, *program.id(), function_name, inputs)
            .to_call(&input_types, &caller_private_key.sk_sig(), &caller_compute_key.pr_sig(), rng)
            .unwrap();

        // Construct the process.
        let process = Process::<CurrentNetwork, CurrentAleo> { program };

        // // Compute the output value.
        // let candidate = program.evaluate(&function_name, &inputs).unwrap();
        // assert_eq!(3, candidate.len());
        // assert_eq!(r2, candidate[0]);
        // assert_eq!(r3, candidate[1]);
        // assert_eq!(r4, candidate[2]);

        use circuit::Eject;

        // Re-run to ensure state continues to work.
        let candidate = process.execute(&call).unwrap();
        assert_eq!(4, candidate.len());
        assert_eq!(r3, candidate[1].eject_value());
        assert_eq!(r4, candidate[2].eject_value());
        assert_eq!(r5, candidate[3].eject_value());

        use circuit::Environment;
        // assert_eq!(24537, CurrentAleo::num_constants());
        // assert_eq!(13, CurrentAleo::num_public());
        // assert_eq!(26454, CurrentAleo::num_private());
        // assert_eq!(26472, CurrentAleo::num_constraints());
        // assert_eq!(90497, CurrentAleo::num_gates());
        assert_eq!(37145, CurrentAleo::num_constants());
        assert_eq!(11, CurrentAleo::num_public());
        assert_eq!(39547, CurrentAleo::num_private());
        assert_eq!(39587, CurrentAleo::num_constraints());
        assert_eq!(132247, CurrentAleo::num_gates());
    }
}
