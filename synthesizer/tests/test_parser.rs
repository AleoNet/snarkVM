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

use snarkvm_synthesizer::Program;

use console::network::{prelude::*, Testnet3};

use std::{
    marker::PhantomData,
    path::{Path, PathBuf},
};

struct ParserTest<F: Parser> {
    path: PathBuf,
    input: String,
    expectation: Option<String>,
    phantom: PhantomData<F>,
}

impl<F: Parser> Test for ParserTest<F> {
    fn load<P: AsRef<Path>>(path: P) -> Result<Self> {
        // Read the test file.
        let input = std::fs::read_to_string(&path).expect("Failed to read input file.");
        // Load the expectation file.
        let expectation = load_expectation(&path);

        Ok(Self { path: path.as_ref().to_path_buf(), input, expectation, phantom: Default::default() })
    }

    fn run(&self) {
        // Run the desired parser.
        let result = F::parse(&self.input);
        // Convert the result into a readable format.
        let output = convert_result(result, &self.input);
        // Check the result against the expectation.
        check_and_log_expectation(&self.path, &self.expectation, &output);
    }
}

#[test]
fn test_program_parser() {
    let runner = Runner::<ParserTest<Program<Testnet3>>>::initialize("./tests/parser/program");
    runner.run();
}
