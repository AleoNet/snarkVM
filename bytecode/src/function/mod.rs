// Copyright (C) 2019-2022 Aleo Systems Inc.
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

use crate::{
    instructions::{Input, Instruction, Output},
    Immediate,
    Memory,
    Register,
};
use snarkvm_circuits::{Parser, ParserResult};

use core::fmt;
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alpha1, alphanumeric1},
    combinator::{opt, recognize},
    multi::{many0, many1, separated_list0, separated_list1},
    sequence::pair,
};

pub struct Function<M: Memory> {
    name: String,
    instructions: Vec<Instruction<M>>,
}

impl<M: Memory> Function<M> {
    /// Adds the given instruction.
    pub fn push_instruction(&mut self, instruction: Instruction<M>) {
        self.instructions.push(instruction);
    }

    /// Evaluates the function, returning the outputs.
    pub fn evaluate(&self) -> Vec<Immediate<M::Environment>> {
        for instruction in &self.instructions {
            instruction.evaluate();
        }
        M::load_outputs()
    }
}

impl<M: Memory> Default for Function<M> {
    fn default() -> Self {
        Self { name: String::new(), instructions: Default::default() }
    }
}

impl<M: Memory> Parser for Function<M> {
    type Environment = M::Environment;

    /// Parses a string into a local function.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        let mut sanitize_whitespace = many0(alt((tag(" "), tag("\n"), tag("\t"))));

        // Parse the whitespace from the string.
        let (string, _) = sanitize_whitespace(string)?;
        // Parse the 'function' keyword from the string.
        let (string, _) = tag("function ")(string)?;
        // Parse the function name from the string.
        let (string, name) = recognize(pair(alpha1, many0(alt((alphanumeric1, tag("_"))))))(string)?;
        // Parse the colon ':' keyword from the string.
        let (string, _) = tag(":")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = sanitize_whitespace(string)?;

        // // Parse the inputs from the string.
        // let (string, inputs) = separated_list1(sanitize_whitespace, Input::parse)(string)?;
        // Parse the instructions from the string.
        let (string, instructions) = separated_list1(sanitize_whitespace, Instruction::parse)(string)?;
        // // Parse the outputs from the string.
        // let (string, outputs) = separated_list1(sanitize_whitespace, Output::parse)(string)?;

        Ok((string, Self { name: name.to_string(), instructions }))
    }
}

impl<M: Memory> fmt::Display for Function<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut output = format!("function {}:\n", self.name);
        for instruction in &self.instructions {
            output += &format!("    {}", instruction);
        }
        write!(f, "{}", output)
    }
}
