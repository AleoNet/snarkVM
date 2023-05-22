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

use console::{account::PrivateKey, network::prelude::*};
use snarkvm_synthesizer::Process;

#[test]
fn test_program_execute() {
    // Load the tests.
    let tests = load_tests::<_, ProgramTest>("./tests/program", "./expectations/program/execute");
    // Initialize a process.
    let mut process = Process::<CurrentNetwork>::load().unwrap();
    // Initialize an RNG.
    let rng = &mut TestRng::default();
    // Initialize a private key.
    let private_key = PrivateKey::new(rng).unwrap();
    // Run each test and compare it against its corresponding expectation.
    for test in &tests {
        // Add the program into the process.
        let program = test.test_program();
        process.add_program(program).unwrap();
        let outputs = test
            .test_cases()
            .iter()
            .map(|(function_name, inputs)| {
                // Authorize the execution.
                let authorization = process
                    .authorize::<CurrentAleo, _>(&private_key, program.id(), function_name, inputs.iter(), rng)
                    .unwrap();
                // Execute the authorization.
                let (response, _, _, _) = process.execute::<CurrentAleo, _>(authorization, rng).unwrap();
                // Extract the output.
                response.outputs().to_vec()
            })
            .collect::<Vec<_>>();
        // Check against the expected output.
        test.check(&outputs).unwrap();
        // Save the output.
        test.save(&outputs).unwrap();
    }
}
