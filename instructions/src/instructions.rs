// Copyright (C) 2019-2021 Aleo Systems Inc.
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

use crate::{InstructionsParser, Rule};

use anyhow::Result;
use pest::{
    iterators::{Pair, Pairs},
    Parser as P,
};

pub enum Instruction {
    Add,
}

// impl Instruction {
//     pub fn new()
// }

pub enum Instructions {
    Add(),
}

impl Instructions {
    pub fn new(instructions: &str) -> Result<()> {
        // Parse the given instructions.
        let instructions = InstructionsParser::parse(Rule::instructions, instructions)?;
        // Iterate over each instruction in line order from top to bottom.
        for (i, instruction) in instructions.enumerate() {
            // Extract the operation from the instruction.
            let operation = instruction.as_rule();
            // Extract the operands from the instruction.
            for (j, operand) in instruction.into_inner().enumerate() {
                let type_ = operand.as_rule();
                let value = operand.as_str();
                println!("{} {}: {:?} {:?} {:?}\n", i, j, operation, type_, value);
            }

            // if instruction.as_rule() == Rule::instruction {
            //     // Rule::add => Self::Add(),
            //     // _ => unimplemented!()
            // };
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use pest::{consumes_to, fails_with, parses_to};

    const ITERATIONS: usize = 100;

    #[test]
    fn test_boolean() {
        parses_to! {
            parser: InstructionsParser,
            input: "true",
            rule: Rule::boolean,
            tokens: [boolean(0, 4, [])]
        };
        parses_to! {
            parser: InstructionsParser,
            input: "false",
            rule: Rule::boolean,
            tokens: [boolean(0, 5, [])]
        };
        fails_with! {
            parser: InstructionsParser,
            input: "abcd",
            rule: Rule::boolean,
            positives: vec![Rule::boolean],
            negatives: vec![],
            pos: 0
        };
    }
}
