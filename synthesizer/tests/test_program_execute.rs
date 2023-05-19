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
