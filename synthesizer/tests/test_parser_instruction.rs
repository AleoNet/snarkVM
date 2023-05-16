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

use console::network::{prelude::*, Testnet3};
use snarkvm_synthesizer::Instruction;

#[test]
fn test_instruction_parser() {
    // Load the tests.
    let tests = load_tests::<_, LineParseTest>("./tests/parser/instruction");
    // For each test, load the corresponding expectation file.
    let expectations =
        tests.iter().map(|test| LineExpectation::load(get_expectation_path(test.path())).unwrap()).collect::<Vec<_>>();
    // Run each test and compare it against its corresponding expectation.
    for (test, expectation) in tests.iter().zip_eq(expectations.iter()) {
        // Run the parser on each of the test strings.
        let outputs = test
            .test_strings()
            .iter()
            .map(|test_string| convert_result(Instruction::<Testnet3>::parse(test_string), test_string))
            .collect::<Vec<_>>();
        // Check against the expected output.
        expectation.check(test.test_strings(), &outputs).unwrap();
        // Save the output.
        expectation.save(&outputs).unwrap();
    }
}
