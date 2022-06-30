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

use crate::{CircuitValue, Program, Stack, StackValue};
use console::{
    account::Address,
    network::prelude::*,
    program::{Identifier, Plaintext, Value, ValueType},
};

pub struct Process<N: Network, A: circuit::Aleo<Network = N>> {
    /// The program (record types, interfaces, functions).
    program: Program<N, A>,
}

impl<N: Network, A: circuit::Aleo<Network = N>> Process<N, A> {
    /// Evaluates a program function on the given inputs.
    #[inline]
    pub fn evaluate(
        &self,
        function_name: &Identifier<N>,
        inputs: &[StackValue<N>],
    ) -> Result<Vec<Value<N, Plaintext<N>>>> {
        // Evaluate the function.
        // Stack::<N, A>::evaluate(self.program.clone(), function_name, inputs)
        self.program.evaluate(function_name, inputs)
    }

    /// Executes a program function on the given inputs.
    #[inline]
    pub fn execute<R: Rng + CryptoRng>(
        &self,
        caller: Address<N>,
        function_name: &Identifier<N>,
        inputs: &[StackValue<N>],
        rng: &mut R,
    ) -> Result<Vec<circuit::Value<A, circuit::Plaintext<A>>>> {
        // Ensure the circuit environment is clean.
        A::reset();

        // Retrieve the function from the program.
        let function = self.program.get_function(function_name)?;
        // Ensure the number of inputs matches the number of input statements.
        if function.inputs().len() != inputs.len() {
            bail!("Expected {} inputs, found {}", function.inputs().len(), inputs.len())
        }

        // Initialize the trace.
        let mut trace = Trace::<N, A>::new(caller, rng)?;

        // Inject the inputs.
        let inputs: Vec<_> = function
            .inputs()
            .iter()
            .map(|i| i.value_type())
            .zip_eq(inputs)
            .map(|(value_type, input)| {
                use circuit::{Eject, Inject, ToBits};

                // Inject the console input into a circuit input.
                let input = match value_type {
                    // Constant inputs are injected as constants.
                    ValueType::Constant(..) => CircuitValue::new(circuit::Mode::Constant, input.clone()),
                    // Public and private inputs are injected as privates. Records inherit their visibility.
                    ValueType::Public(..) | ValueType::Private(..) | ValueType::Record(..) => {
                        CircuitValue::new(circuit::Mode::Private, input.clone())
                    }
                };

                // Compute the input leaf.
                let input_leaf = match &input {
                    // TODO (howardwu): Handle encrypting the private input case.
                    CircuitValue::Plaintext(..) => A::hash_bhp1024(&input.to_bits_le()),
                    CircuitValue::Record(record) => {
                        // Compute the record commitment.
                        let commitment = record.to_commitment();
                        // TODO (howardwu): Compute the serial number.
                        // Compute the serial number.
                        let serial_number = commitment;
                        // Output the serial number.
                        serial_number
                    }
                };

                // Eject to the console input leaf.
                let console_input_leaf = input_leaf.eject_value();
                // Inject the input leaf as a public input.
                let candidate_leaf = circuit::Field::<A>::new(circuit::Mode::Public, console_input_leaf);
                // Ensure the candidate input leaf matches the computed input leaf.
                A::assert_eq(candidate_leaf, &input_leaf);

                // Add the console input leaf to the trace.
                trace.add_input(console_input_leaf)?;

                Ok::<_, Error>(input)
            })
            .try_collect()?;

        // Execute the function.
        let outputs = Stack::<N, A>::execute_transition(self.program.clone(), function_name, &inputs)?;

        // Load the outputs.
        outputs.iter().try_for_each(|output| {
            use circuit::{Eject, Inject, ToBits};

            // Compute the output leaf.
            let output_leaf = match output {
                // TODO (howardwu): Handle encrypting the private output case.
                circuit::Value::Constant(..) | circuit::Value::Public(..) | circuit::Value::Private(..) => {
                    A::hash_bhp1024(&output.to_bits_le())
                }
                circuit::Value::Record(record) => record.to_commitment(),
            };

            // Eject to the console output leaf.
            let console_output_leaf = output_leaf.eject_value();
            // Inject the output leaf as a public input.
            let candidate_leaf = circuit::Field::<A>::new(circuit::Mode::Public, console_output_leaf);
            // Ensure the candidate output leaf matches the computed output leaf.
            A::assert_eq(candidate_leaf, &output_leaf);

            // Add the console output leaf to the trace.
            trace.add_output(console_output_leaf)?;

            Ok::<_, Error>(())
        })?;

        // Finalize the trace.
        trace.finalize()?;

        println!("{:?}", trace.leaves());
        println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());
        let (num_constant, num_public, num_private, num_constraints, num_gates) = A::count();
        println!(
            "Count(Constant: {num_constant}, Public: {num_public}, Private: {num_private}, Constraints: {num_constraints}, Gates: {num_gates})"
        );

        Ok(outputs)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use circuit::network::AleoV0;
    use console::{
        account::{PrivateKey, ViewKey},
        network::Testnet3,
        program::Record,
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

        // Construct the process.
        let process = Process::<CurrentNetwork, CurrentAleo> { program };

        // Initialize the RNG.
        let rng = &mut test_crypto_rng();

        // Initialize a new caller account.
        let caller_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let _caller_view_key = ViewKey::try_from(&caller_private_key).unwrap();
        let caller = Address::try_from(&caller_private_key).unwrap();

        // // Compute the output value.
        // let candidate = program.evaluate(&function_name, &[r0.clone(), r1.clone()]).unwrap();
        // assert_eq!(3, candidate.len());
        // assert_eq!(r2, candidate[0]);
        // assert_eq!(r3, candidate[1]);
        // assert_eq!(r4, candidate[2]);

        use circuit::Eject;

        // Re-run to ensure state continues to work.
        let candidate = process.execute(caller, &function_name, &[r0, r1, r2], rng).unwrap();
        assert_eq!(4, candidate.len());
        assert_eq!(r3, candidate[1].eject_value());
        assert_eq!(r4, candidate[2].eject_value());
        assert_eq!(r5, candidate[3].eject_value());
    }
}
