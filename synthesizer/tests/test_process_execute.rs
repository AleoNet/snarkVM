// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

mod utilities;
use utilities::*;

use console::{
    account::PrivateKey,
    network::prelude::*,
    program::{Identifier, Literal, Value},
    types::Boolean,
};
use synthesizer_process::Process;

use rayon::prelude::*;

#[test]
fn test_process_execute() {
    // Load the tests.
    let tests = load_tests::<_, ProgramTest>("./tests/program", "./expectations/process/execute");
    // Initialize a process.
    let process = Process::<CurrentNetwork>::load().unwrap();

    // Run each test and compare it against its corresponding expectation.
    tests.par_iter().for_each(|test| {
        // Add the program into the process.
        let mut process = process.clone();
        let program = test.program();
        process.add_program(program).unwrap();

        // Initialize the RNG.
        let rng = &mut match test.randomness() {
            None => TestRng::default(),
            Some(randomness) => TestRng::fixed(randomness),
        };

        let outputs = test
            .cases()
            .iter()
            .map(|value| {
                // Extract the function name, inputs, and optional private key.
                let value = value.as_mapping().expect("expected mapping for test case");
                let function_name = Identifier::<CurrentNetwork>::from_str(
                    value
                        .get("function")
                        .expect("expected function name for test case")
                        .as_str()
                        .expect("expected string for function name"),
                )
                .expect("unable to parse function name");
                let inputs = value
                    .get("inputs")
                    .expect("expected inputs for test case")
                    .as_sequence()
                    .expect("expected sequence for inputs")
                    .iter()
                    .map(|input| match &input {
                        serde_yaml::Value::Bool(bool) => {
                            Value::<CurrentNetwork>::from(Literal::Boolean(Boolean::new(*bool)))
                        }
                        _ => Value::<CurrentNetwork>::from_str(input.as_str().expect("expected string for input"))
                            .expect("unable to parse input"),
                    })
                    .collect_vec();
                let private_key = match value.get("private_key") {
                    Some(private_key) => PrivateKey::<CurrentNetwork>::from_str(
                        private_key.as_str().expect("expected string for private key"),
                    )
                    .expect("unable to parse private key"),
                    None => PrivateKey::new(rng).unwrap(),
                };

                let mut run_test = || -> serde_yaml::Value {
                    // Authorize the execution.
                    let authorization = match process.authorize::<CurrentAleo, _>(
                        &private_key,
                        program.id(),
                        function_name,
                        inputs.iter(),
                        rng,
                    ) {
                        Ok(authorization) => authorization,
                        Err(err) => return serde_yaml::Value::String(err.to_string()),
                    };
                    // Execute the authorization.
                    let response = match process.execute::<CurrentAleo>(authorization) {
                        Ok((response, _)) => response,
                        Err(err) => return serde_yaml::Value::String(err.to_string()),
                    };
                    // Extract the output.
                    serde_yaml::Value::Sequence(
                        response
                            .outputs()
                            .iter()
                            .cloned()
                            .map(|output| serde_yaml::Value::String(output.to_string()))
                            .collect_vec(),
                    )
                };
                run_test()
            })
            .collect::<Vec<_>>();
        // Check against the expected output.
        test.check(&outputs).unwrap();
        // Save the output.
        test.save(&outputs).unwrap();
    });
}
