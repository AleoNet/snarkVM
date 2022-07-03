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
    program::{Request, Response},
};

pub struct Process<N: Network, A: circuit::Aleo<Network = N>> {
    /// The program (record types, interfaces, functions).
    program: Program<N, A>,
}

impl<N: Network, A: circuit::Aleo<Network = N>> Process<N, A> {
    /// Evaluates a program function on the given request.
    #[inline]
    pub fn evaluate(&self, request: &Request<N>) -> Result<Response<N>> {
        // Ensure the request is well-formed.
        ensure!(request.verify(), "Request is invalid");

        // Retrieve the inputs.
        let inputs = request.inputs();
        // Retrieve the number of inputs.
        let num_inputs = inputs.len();
        // Retrieve the function from the program.
        let function = self.program.get_function(request.function_name())?;
        // Ensure the number of inputs matches the number of input statements.
        if function.inputs().len() != num_inputs {
            bail!("Expected {} inputs, found {num_inputs}", function.inputs().len())
        }

        // Prepare the stack.
        let mut stack = Stack::<N, A>::new(Some(self.program.clone()))?;
        // Evaluate the function.
        let outputs = stack.evaluate_function(&function, inputs)?;

        // Load the output types.
        let output_types = function.outputs().iter().map(|output| *output.value_type()).collect::<Vec<_>>();
        // Compute the response.
        let response = Response::new(num_inputs, request.tvk(), outputs, &output_types)?;

        // Initialize the trace.
        let mut trace = Trace::<N>::new(request, &response)?;
        // Finalize the trace.
        trace.finalize()?;
        println!("{:?}", trace.leaves());

        Ok(response)
    }

    /// Executes a program function on the given request.
    #[inline]
    pub fn execute(&self, request: &Request<N>) -> Result<circuit::Response<A>> {
        // Ensure the request is well-formed.
        ensure!(request.verify(), "Request is invalid");

        // Retrieve the inputs.
        let inputs = request.inputs();
        // Retrieve the number of inputs.
        let num_inputs = inputs.len();
        // Retrieve the function from the program.
        let function = self.program.get_function(request.function_name())?;
        // Ensure the number of inputs matches the number of input statements.
        if function.inputs().len() != num_inputs {
            bail!("Expected {} inputs, found {num_inputs}", function.inputs().len())
        }

        // Ensure the circuit environment is clean.
        A::reset();

        let response = {
            use circuit::Inject;

            // Inject the transition view key `tvk` as `Mode::Public`.
            let tvk = circuit::Field::<A>::new(circuit::Mode::Public, *request.tvk());
            // Inject the request as `Mode::Private`.
            let request = circuit::Request::new(circuit::Mode::Private, request.clone());
            // Ensure the `tvk` matches.
            A::assert_eq(request.tvk(), tvk);
            // Ensure the request has a valid signature and serial numbers.
            A::assert(request.verify());

            #[cfg(debug_assertions)]
            Self::log_circuit("Request Authentication");

            // Prepare the stack.
            let mut stack = Stack::<N, A>::new(Some(self.program.clone()))?;
            // Execute the function.
            let outputs = stack.execute_function(&function, request.inputs())?;

            #[cfg(debug_assertions)]
            Self::log_circuit(format!("Function '{}()'", function.name()));

            // Load the output types.
            let output_types = function.outputs().iter().map(|output| *output.value_type()).collect::<Vec<_>>();

            circuit::Response::from_outputs(num_inputs, request.tvk(), outputs, &output_types)
        };

        // A::assert(response.verify(num_inputs, request.caller(), request.tvk()));

        #[cfg(debug_assertions)]
        Self::log_circuit("Response");

        // // Initialize the trace.
        // let mut trace = Trace::<N>::new(request, &response)?;
        // // Finalize the trace.
        // trace.finalize()?;
        // println!("{:?}", trace.leaves());

        Ok(response)
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
        account::{ComputeKey, PrivateKey, ViewKey},
        network::Testnet3,
        program::{Identifier, Plaintext, Record, Request, StackValue, ValueType},
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
        let r3 = StackValue::Plaintext(Plaintext::from_str("19field").unwrap());
        let r4 = StackValue::Plaintext(Plaintext::from_str("11field").unwrap());
        let r5 = StackValue::Plaintext(Plaintext::from_str("8field").unwrap());

        // Initialize the RNG.
        let rng = &mut test_crypto_rng();

        // Initialize a new caller account.
        let caller_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let caller_compute_key = ComputeKey::try_from(&caller_private_key).unwrap();
        let _caller_view_key = ViewKey::try_from(&caller_private_key).unwrap();

        // Construct the inputs and input types.
        let inputs = vec![r0, r1, r2.clone()];
        let input_types = vec![
            ValueType::from_str("field.private").unwrap(),
            ValueType::from_str("field.public").unwrap(),
            ValueType::from_str("token.record").unwrap(),
        ];

        // Compute the signed request.
        let request = Request::sign(
            &caller_private_key.sk_sig(),
            &caller_compute_key.pr_sig(),
            *program.id(),
            function_name,
            inputs,
            &input_types,
            rng,
        )
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

        // Execute the request.
        let response = process.execute(&request).unwrap();
        let candidate = response.outputs();
        assert_eq!(4, candidate.len());
        assert_eq!(r2, candidate[0].eject_value());
        assert_eq!(r3, candidate[1].eject_value());
        assert_eq!(r4, candidate[2].eject_value());
        assert_eq!(r5, candidate[3].eject_value());

        use circuit::Environment;

        assert_eq!(36662, CurrentAleo::num_constants());
        assert_eq!(11, CurrentAleo::num_public());
        assert_eq!(41630, CurrentAleo::num_private());
        assert_eq!(41678, CurrentAleo::num_constraints());
        assert_eq!(159119, CurrentAleo::num_gates());
    }
}
