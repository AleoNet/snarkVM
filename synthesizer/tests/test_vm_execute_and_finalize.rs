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
use snarkvm_synthesizer::{ConsensusStore, Process, VM};
use snarkvm_synthesizer::helpers::memory::ConsensusMemory;

#[test]
fn test_vm_execute_and_finalize() {
    // Load the tests.
    let tests = load_tests::<_, ProgramTest>("./tests/program", "./expectations/vm/execute_and_finalize");


    // Run each test and compare it against its corresponding expectation.
    for test in &tests {
        // Initialize the RNG.
        let rng = &mut match test.randomness() {
            None => TestRng::default(),
            Some(randomness) => TestRng::fixed(randomness),
        };

        // Sample a private key.
        let private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();

        // Initialize a VM.
        let vm: VM<CurrentNetwork, ConsensusMemory<CurrentNetwork>> = VM::from(ConsensusStore::open(None).unwrap()).unwrap();

        // Initialize the genesis block.
        let genesis = vm.genesis(&private_key, rng).unwrap();

        // Fetch the unspent records.
        let records = genesis.transitions().cloned().flat_map(Transition::into_records).collect::<IndexMap<_, _>>();

        // Select a record to spend.
        let view_key = ViewKey::try_from(private_key).unwrap();
        let records = records.values().map(|record| record.decrypt(&view_key).unwrap()).collect();

        // Calculate the number of transactions and create records for each.

        // Update the VM.
        vm.add_next_block(&genesis).unwrap();

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
                    let response = match process.execute::<CurrentAleo, _>(authorization, rng) {
                        Ok((response, _, _, _)) => response,
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
    }
}
