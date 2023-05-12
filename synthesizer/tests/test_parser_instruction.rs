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

use std::{marker::PhantomData, path::Path};

/// Defines a test that runs a parser on a given instruction.
pub struct TestParserInstruction<F: Parser> {
    inputs: Vec<String>,
    expectation: LineExpectation,
    phantom: PhantomData<F>,
}

impl<F: Parser> Test for TestParserInstruction<F> {
    fn load<P: AsRef<Path>>(path: P) -> Result<Self> {
        // Read the test file.
        let inputs = std::fs::read_to_string(&path)
            .expect("Failed to read instruction file.")
            .lines()
            .map(|l| l.to_string())
            .collect();
        // Load the expectation file.
        let expectation = LineExpectation::load(get_expectation_path(&path))?;

        Ok(Self { inputs, expectation, phantom: Default::default() })
    }

    fn run(&self) {
        let outputs = self.inputs.iter().map(|input| convert_result(F::parse(input), input)).collect();
        // Check the results against the expectations.
        self.expectation.check(&self.inputs, &outputs).expect("Failed to check expectation.");
        // Save the results to the expectation file.
        self.expectation.save(&outputs).expect("Failed to save expectation.");
    }
}

#[test]
fn test_instruction_parser() {
    let runner = Runner::<TestParserInstruction<Instruction<Testnet3>>>::initialize("./tests/parser/instruction");
    runner.run();
}
