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

use console::network::prelude::*;
use snarkvm_synthesizer::Program;

#[test]
fn test_program_parse() {
    // Load the tests.
    let tests = load_tests::<_, FileParseTest>("./tests/parser/program", "./expectations/parser/program");
    // Run each test and compare it against its corresponding expectation.
    for test in &tests {
        // Run the parser on the test string.
        let test_string = test.test_string();
        let output = convert_result(Program::<CurrentNetwork>::parse(test_string), test_string);
        // Check against the expected output.
        test.check(&output).unwrap();
        // Save the output.
        test.save(&output).unwrap();
    }
}
