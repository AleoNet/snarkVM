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

mod closure;
mod finalize;
mod function;
mod instruction;

use crate::{
    program::{Instruction, Program},
    CallMetrics,
    CallStack,
    Closure,
    FinalizeOperation,
    Operand,
    Registers,
    Stack,
    Transition,
};
use console::{
    account::Address,
    network::prelude::*,
    program::{Identifier, Literal, Plaintext, Response, Value},
    types::Field,
};

use aleo_std::prelude::{finish, lap, timer};

impl<N: Network> Stack<N> {
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

#[cfg(test)]
mod tests {
    use super::*;
    use circuit::network::AleoV0;
    use console::{
        account::{Address, PrivateKey},
        network::Testnet3,
        program::{Plaintext, Record, Value},
        types::Field,
    };

    use crate::{Execution, Inclusion};
    use parking_lot::RwLock;
    use std::sync::Arc;

    type CurrentNetwork = Testnet3;
    type CurrentAleo = AleoV0;

    #[test]
    fn test_program_evaluate_function() {
        let program = Program::<CurrentNetwork>::from_str(
            r"
    program example.aleo;

    function foo:
        input r0 as field.public;
        input r1 as field.private;
        add r0 r1 into r2;
        output r2 as field.private;
    ",
        )
        .unwrap();

        // Declare the function name.
        let function_name = Identifier::from_str("foo").unwrap();
        // Declare the function inputs.
        let inputs = [
            Value::<CurrentNetwork>::Plaintext(Plaintext::from_str("2field").unwrap()),
            Value::Plaintext(Plaintext::from_str("3field").unwrap()),
        ];

        // Construct the process.
        let process = crate::process::test_helpers::sample_process(&program);

        // Compute the authorization.
        let authorization = {
            // Initialize an RNG.
            let rng = &mut TestRng::default();

            // Initialize caller private key.
            let caller_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();

            // Authorize the function call.
            let authorization = process
                .authorize::<CurrentAleo, _>(&caller_private_key, program.id(), function_name, inputs.iter(), rng)
                .unwrap();
            assert_eq!(authorization.len(), 1);
            authorization
        };

        // Retrieve the stack.
        let stack = process.get_stack(program.id()).unwrap();

        // Declare the expected output.
        let expected = Value::Plaintext(Plaintext::<CurrentNetwork>::from_str("5field").unwrap());

        // Run the function.
        let response =
            stack.evaluate_function::<CurrentAleo>(CallStack::evaluate(authorization.replicate()).unwrap()).unwrap();
        let candidate = response.outputs();
        assert_eq!(1, candidate.len());
        assert_eq!(expected, candidate[0]);

        // Re-run to ensure state continues to work.
        let response = stack.evaluate_function::<CurrentAleo>(CallStack::evaluate(authorization).unwrap()).unwrap();
        let candidate = response.outputs();
        assert_eq!(1, candidate.len());
        assert_eq!(expected, candidate[0]);
    }

    #[test]
    fn test_program_evaluate_struct_and_function() {
        // Initialize a new program.
        let (string, program) = Program::<CurrentNetwork>::parse(
            r"
program example.aleo;

struct message:
    first as field;
    second as field;

function compute:
    input r0 as message.private;
    add r0.first r0.second into r1;
    output r1 as field.private;",
        )
        .unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");

        // Declare the function name.
        let function_name = Identifier::from_str("compute").unwrap();
        // Declare the input value.
        let input =
            Value::<CurrentNetwork>::Plaintext(Plaintext::from_str("{ first: 2field, second: 3field }").unwrap());
        // Declare the expected output value.
        let expected = Value::Plaintext(Plaintext::from_str("5field").unwrap());

        // Construct the process.
        let process = crate::process::test_helpers::sample_process(&program);

        // Compute the authorization.
        let authorization = {
            // Initialize an RNG.
            let rng = &mut TestRng::default();

            // Initialize caller private key.
            let caller_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();

            // Authorize the function call.
            let authorization = process
                .authorize::<CurrentAleo, _>(&caller_private_key, program.id(), function_name, [input].iter(), rng)
                .unwrap();
            assert_eq!(authorization.len(), 1);
            authorization
        };

        // Retrieve the stack.
        let stack = process.get_stack(program.id()).unwrap();

        // Compute the output value.
        let response =
            stack.evaluate_function::<CurrentAleo>(CallStack::evaluate(authorization.replicate()).unwrap()).unwrap();
        let candidate = response.outputs();
        assert_eq!(1, candidate.len());
        assert_eq!(expected, candidate[0]);

        // Re-run to ensure state continues to work.
        let response = stack.evaluate_function::<CurrentAleo>(CallStack::evaluate(authorization).unwrap()).unwrap();
        let candidate = response.outputs();
        assert_eq!(1, candidate.len());
        assert_eq!(expected, candidate[0]);
    }

    #[test]
    fn test_program_evaluate_record_and_function() {
        // Initialize a new program.
        let (string, program) = Program::<CurrentNetwork>::parse(
            r"
program token.aleo;

record token:
    owner as address.private;
    gates as u64.private;
    token_amount as u64.private;

function compute:
    input r0 as token.record;
    add r0.token_amount r0.token_amount into r1;
    output r1 as u64.private;",
        )
        .unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");

        // Declare the function name.
        let function_name = Identifier::from_str("compute").unwrap();

        // Initialize an RNG.
        let rng = &mut TestRng::default();

        // Initialize caller private key.
        let caller_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let caller = Address::try_from(&caller_private_key).unwrap();

        // Declare the input value.
        let input_record = Record::from_str(&format!(
            "{{ owner: {caller}.private, gates: 5u64.private, token_amount: 100u64.private, _nonce: 0group.public }}"
        ))
        .unwrap();
        let input = Value::<CurrentNetwork>::Record(input_record);

        // Declare the expected output value.
        let expected = Value::Plaintext(Plaintext::from_str("200u64").unwrap());

        // Construct the process.
        let process = crate::process::test_helpers::sample_process(&program);

        // Authorize the function call.
        let authorization = process
            .authorize::<CurrentAleo, _>(&caller_private_key, program.id(), function_name, [input].iter(), rng)
            .unwrap();
        assert_eq!(authorization.len(), 1);

        // Retrieve the stack.
        let stack = process.get_stack(program.id()).unwrap();

        // Compute the output value.
        let response =
            stack.evaluate_function::<CurrentAleo>(CallStack::evaluate(authorization.replicate()).unwrap()).unwrap();
        let candidate = response.outputs();
        assert_eq!(1, candidate.len());
        assert_eq!(expected, candidate[0]);

        // Re-run to ensure state continues to work.
        let response = stack.evaluate_function::<CurrentAleo>(CallStack::evaluate(authorization).unwrap()).unwrap();
        let candidate = response.outputs();
        assert_eq!(1, candidate.len());
        assert_eq!(expected, candidate[0]);
    }

    #[test]
    fn test_program_evaluate_call() {
        // Initialize a new program.
        let (string, program) = Program::<CurrentNetwork>::parse(
            r"
program example_call.aleo;

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
    call execute r0 r1 into r2 r3 r4;
    output r2 as field.private;
    output r3 as field.private;
    output r4 as field.private;",
        )
        .unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");

        // Declare the function name.
        let function_name = Identifier::from_str("compute").unwrap();

        // Declare the input value.
        let r0 = Value::<CurrentNetwork>::Plaintext(Plaintext::from_str("3field").unwrap());
        let r1 = Value::<CurrentNetwork>::Plaintext(Plaintext::from_str("5field").unwrap());

        // Declare the expected output value.
        let r2 = Value::Plaintext(Plaintext::from_str("19field").unwrap());
        let r3 = Value::Plaintext(Plaintext::from_str("11field").unwrap());
        let r4 = Value::Plaintext(Plaintext::from_str("8field").unwrap());

        {
            // Construct the process.
            let process = crate::process::test_helpers::sample_process(&program);
            // Check that the circuit key can be synthesized.
            process.synthesize_key::<CurrentAleo, _>(program.id(), &function_name, &mut TestRng::default()).unwrap();
        }

        // Construct the process.
        let process = crate::process::test_helpers::sample_process(&program);

        // Compute the authorization.
        let authorization = {
            // Initialize an RNG.
            let rng = &mut TestRng::default();

            // Initialize caller private key.
            let caller_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();

            // Authorize the function call.
            let authorization = process
                .authorize::<CurrentAleo, _>(
                    &caller_private_key,
                    program.id(),
                    function_name,
                    [r0.clone(), r1.clone()].iter(),
                    rng,
                )
                .unwrap();
            assert_eq!(authorization.len(), 1);
            authorization
        };

        // Retrieve the stack.
        let stack = process.get_stack(program.id()).unwrap();

        // Compute the output value.
        let response =
            stack.evaluate_function::<CurrentAleo>(CallStack::evaluate(authorization.replicate()).unwrap()).unwrap();
        let candidate = response.outputs();
        assert_eq!(3, candidate.len());
        assert_eq!(r2, candidate[0]);
        assert_eq!(r3, candidate[1]);
        assert_eq!(r4, candidate[2]);

        // Re-run to ensure state continues to work.
        let response = stack.evaluate_function::<CurrentAleo>(CallStack::evaluate(authorization).unwrap()).unwrap();
        let candidate = response.outputs();
        assert_eq!(3, candidate.len());
        assert_eq!(r2, candidate[0]);
        assert_eq!(r3, candidate[1]);
        assert_eq!(r4, candidate[2]);

        use circuit::Environment;

        // Ensure the environment is clean.
        assert_eq!(0, CurrentAleo::num_constants());
        assert_eq!(1, CurrentAleo::num_public());
        assert_eq!(0, CurrentAleo::num_private());
        assert_eq!(0, CurrentAleo::num_constraints());

        // Initialize an RNG.
        let rng = &mut TestRng::default();
        // Initialize a burner private key.
        let burner_private_key = PrivateKey::new(rng).unwrap();
        // Authorize the function call, with a burner private key.
        let authorization = process
            .authorize::<CurrentAleo, _>(&burner_private_key, program.id(), function_name, [r0, r1].iter(), rng)
            .unwrap();
        assert_eq!(authorization.len(), 1);

        // Re-run to ensure state continues to work.
        let execution = Arc::new(RwLock::new(Execution::new()));
        let inclusion = Arc::new(RwLock::new(Inclusion::new()));
        let metrics = Arc::new(RwLock::new(Vec::new()));
        let call_stack = CallStack::execute(authorization, execution, inclusion, metrics).unwrap();
        let response = stack.execute_function::<CurrentAleo, _>(call_stack, rng).unwrap();
        let candidate = response.outputs();
        assert_eq!(3, candidate.len());
        assert_eq!(r2, candidate[0]);
        assert_eq!(r3, candidate[1]);
        assert_eq!(r4, candidate[2]);
    }

    #[test]
    fn test_program_evaluate_cast() {
        // Initialize a new program.
        let (string, program) = Program::<CurrentNetwork>::parse(
            r"
program token_with_cast.aleo;

record token:
    owner as address.private;
    gates as u64.private;
    token_amount as u64.private;

function compute:
    input r0 as token.record;
    cast r0.owner r0.gates r0.token_amount into r1 as token.record;
    output r1 as token.record;",
        )
        .unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");

        // Declare the function name.
        let function_name = Identifier::from_str("compute").unwrap();

        // Initialize an RNG.
        let rng = &mut TestRng::default();

        // Initialize caller private key.
        let caller_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let caller = Address::try_from(&caller_private_key).unwrap();

        // Declare the input value.
        let input_record = Record::from_str(&format!(
            "{{ owner: {caller}.private, gates: 5u64.private, token_amount: 100u64.private, _nonce: 0group.public }}"
        ))
        .unwrap();
        let input = Value::<CurrentNetwork>::Record(input_record);

        // Construct the process.
        let process = crate::process::test_helpers::sample_process(&program);

        // Authorize the function call.
        let authorization = process
            .authorize::<CurrentAleo, _>(&caller_private_key, program.id(), function_name, [input].iter(), rng)
            .unwrap();
        assert_eq!(authorization.len(), 1);
        let request = authorization.peek_next().unwrap();

        // Compute the encryption randomizer as `HashToScalar(tvk || index)`.
        let randomizer = CurrentNetwork::hash_to_scalar_psd2(&[*request.tvk(), Field::from_u64(1)]).unwrap();
        let nonce = CurrentNetwork::g_scalar_multiply(&randomizer);

        // Declare the expected output value.
        let expected = Value::from_str(&format!(
            "{{ owner: {caller}.private, gates: 5u64.private, token_amount: 100u64.private, _nonce: {nonce}.public }}"
        ))
        .unwrap();

        // Retrieve the stack.
        let stack = process.get_stack(program.id()).unwrap();

        // Compute the output value.
        let response =
            stack.evaluate_function::<CurrentAleo>(CallStack::evaluate(authorization.replicate()).unwrap()).unwrap();
        let candidate = response.outputs();
        assert_eq!(1, candidate.len());
        assert_eq!(expected, candidate[0]);

        // Re-run to ensure state continues to work.
        let response = stack.evaluate_function::<CurrentAleo>(CallStack::evaluate(authorization).unwrap()).unwrap();
        let candidate = response.outputs();
        assert_eq!(1, candidate.len());
        assert_eq!(expected, candidate[0]);
    }
}
