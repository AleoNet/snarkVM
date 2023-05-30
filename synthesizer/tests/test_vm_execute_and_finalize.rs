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
    program::{Identifier, Value},
};
use snarkvm_synthesizer::{helpers::memory::ConsensusMemory, ConsensusStore, VM};

#[test]
fn test_vm_execute_and_finalize() {
    // Load the tests.
    let tests = load_tests::<_, ProgramTest>("./tests/program", "./expectations/vm/execute_and_finalize");

    // Initialize a VM.
    let vm: VM<CurrentNetwork, ConsensusMemory<CurrentNetwork>> =
        VM::from(ConsensusStore::open(None).unwrap()).unwrap();

    // Run each test and compare it against its corresponding expectation.
    for test in &tests {
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
                    .map(|input| {
                        Value::<CurrentNetwork>::from_str(input.as_str().expect("expected string for input"))
                            .expect("unable to parse input")
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
                    let mut output = serde_yaml::Mapping::new();
                    // Execute the function.
                    let transaction = match vm.execute(
                        &private_key,
                        (test.program().id(), function_name),
                        inputs.iter(),
                        None,
                        None,
                        rng,
                    ) {
                        Ok(transaction) => transaction,
                        Err(err) => {
                            output.insert(
                                serde_yaml::Value::String("execute".to_string()),
                                serde_yaml::Value::String(err.to_string()),
                            );
                            return serde_yaml::Value::Mapping(output);
                        }
                    };
                    // For each transition in the transaction, extract the transition outputs and the inputs for finalize.
                    let mut execute = serde_yaml::Mapping::new();
                    for transition in transaction.transitions() {
                        let mut transition_output = serde_yaml::Mapping::new();
                        let outputs = transition
                            .outputs()
                            .iter()
                            .map(|output| serde_yaml::Value::String(output.to_string()))
                            .collect::<Vec<_>>();
                        transition_output.insert(
                            serde_yaml::Value::String("outputs".to_string()),
                            serde_yaml::Value::Sequence(outputs),
                        );
                        let finalize = match transition.finalize() {
                            None => vec![],
                            Some(finalize) => finalize
                                .iter()
                                .map(|input| serde_yaml::Value::String(input.to_string()))
                                .collect::<Vec<_>>(),
                        };
                        transition_output.insert(
                            serde_yaml::Value::String("finalize".to_string()),
                            serde_yaml::Value::Sequence(finalize),
                        );
                        execute.insert(
                            serde_yaml::Value::String(format!(
                                "{}/{}",
                                transition.program_id(),
                                transition.function_name()
                            )),
                            serde_yaml::Value::Mapping(transition_output),
                        );
                    }
                    output
                        .insert(serde_yaml::Value::String("execute".to_string()), serde_yaml::Value::Mapping(execute));
                    // Finalize the transaction.
                    let transactions = match vm.speculate([transaction].iter()) {
                        Ok(transactions) => {
                            output.insert(
                                serde_yaml::Value::String("speculate".to_string()),
                                serde_yaml::Value::String("`speculate` succeeded.".to_string()),
                            );
                            transactions
                        }
                        Err(err) => {
                            output.insert(
                                serde_yaml::Value::String("speculate".to_string()),
                                serde_yaml::Value::String(err.to_string()),
                            );
                            return serde_yaml::Value::Mapping(output);
                        }
                    };
                    match vm.finalize(&transactions) {
                        Ok(_) => {
                            output.insert(
                                serde_yaml::Value::String("finalize".to_string()),
                                serde_yaml::Value::String("`finalize` succeeded.".to_string()),
                            );
                        }
                        Err(err) => {
                            output.insert(
                                serde_yaml::Value::String("finalize".to_string()),
                                serde_yaml::Value::String(err.to_string()),
                            );
                        }
                    };
                    serde_yaml::Value::Mapping(output)
                };

                run_test()
            })
            .collect::<Vec<_>>();
        // Check against the expected output.
        test.check(&outputs).unwrap();
        // Save the output.
        test.save(&outputs).unwrap();
    }
}
