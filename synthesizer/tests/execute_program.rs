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

mod utilities;
use utilities::*;

use circuit::AleoV0;
use console::network::{prelude::*, Network, Testnet3};
use console::program::{Identifier, Value};
use snarkvm_synthesizer::{Program, Process};

use std::{marker::PhantomData, path::Path};
use serde_yaml::Sequence;
use console::account::PrivateKey;

/// Defines a test that runs a parser on a given program.
pub struct ExecuteProgram<N: Network> {
    program: Program<N>,
    cases: Vec<(Identifier<N>, Vec<Value<N>>)>,
    expectation: LineExpectation,
}

impl<N: Network> Test for ExecuteProgram<N> {
    type Config = Process<N>;

    fn load<P: AsRef<Path>>(path: P) -> Result<Self> {
        // Read the test file.
        let input = std::fs::read_to_string(&path).expect("Failed to read program file.");
        // Parse out the test cases.
        let first_comment_start = input.find("/*").expect("expected a comment opener in configuration");
        let end_first_comment = input[first_comment_start + 2..].find("*/").expect("expected a comment closer in configuration");
        let comment_inner = &input[first_comment_start + 2..first_comment_start + 2 + end_first_comment];
        let sequence: Sequence = serde_yaml::from_str(comment_inner).expect("invalid yaml in configuration");
        let mut cases = Vec::new();
        for value in sequence {
            let mut case = Vec::new();
            let (name, args) = value.as_sequence().expect("invalid sequence of arguments in configuration").split_first().expect("expected at least one argument in configuration");
            let name = Identifier::<N>::from_str(name.as_str().expect("invalid function name in configuration")).unwrap();
            for arg in args {
                case.push(Value::from_str(arg.as_str().expect("invalid argument in configuration")).unwrap());
            }
            cases.push((name, case));
        }
        // Parse out the program.
        let program = Program::<N>::from_str(&input[end_first_comment + 2]).expect("invalid test program");
        // Load the expectation file.
        let expectation = LineExpectation::load(get_expectation_path(&path))?;

        Ok(Self { program, cases, expectation })
    }

    fn run(&self, process: &mut Self::Config) {
        // Initialize an RNG.
        let rng = &mut TestRng::default();
        // Initialize a private key,
        let private_key = PrivateKey::new(rng).unwrap();
        // Add the program to the process.
        process.add_program(&self.program).unwrap();

        // Execute each test case.
        let mut cases = Vec::new();
        let mut outputs = Vec::new();
        for (function_name, inputs) in &self.cases {
            // Add the test case to the list of cases.
            cases.push(format!("{}({})", function_name, inputs.iter().map(|input| input.to_string()).collect::<Vec<_>>().join(", ")));
            // Create an authorization.
            let authorization = process.authorize::<AleoV0, _>(&private_key, self.program.id(), function_name, inputs.iter(), rng).unwrap();
            // Execute the program and get the output.
            let output  = match process.execute(authorization, rng) {
                Ok((response,_, _, _)) => response.outputs().iter().join(", "),
                Err(error) => format!("error: {}", error),
            };
            // Add the output to the list of outputs.
            outputs.push(output);
        }
        // Check the result against the expectation.
        self.expectation.check(&cases, &outputs).expect("Failed to check expectation.");
        // Save the result to the expectation file.
        self.expectation.save(&outputs).expect("Failed to save expectation.");
    }
}

#[test]
fn test_program_parser() {
    let runner = ProcessRunner::<_, ExecuteProgram<Testnet3>>::initialize("./tests/execute");
    runner.run();
}
