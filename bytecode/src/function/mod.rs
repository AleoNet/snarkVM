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

pub mod input;
pub use input::*;

pub mod output;
pub use output::*;

use crate::{instructions::Instruction, Immediate, Memory, Operation, Sanitizer};
use snarkvm_circuits::{Parser, ParserResult};

use core::fmt;
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alpha1, alphanumeric1},
    combinator::recognize,
    multi::{many0, many1},
    sequence::pair,
};

pub struct Function<M: Memory> {
    name: String,
    inputs: Vec<Input<M>>,
    instructions: Vec<Instruction<M>>,
    // instructions: Vec<Box<dyn Operation<Memory = M, Environment = M::Environment>>>,
    outputs: Vec<Output<M>>,
}

impl<M: Memory> Function<M> {
    /// Evaluates the function, returning the outputs.
    pub fn evaluate(&self) -> Vec<Immediate<M::Environment>> {
        self.inputs.iter().for_each(Operation::evaluate);
        self.instructions.iter().for_each(Instruction::evaluate);
        self.outputs.iter().for_each(Operation::evaluate);
        M::load_outputs()
    }
}

impl<M: Memory> Default for Function<M> {
    fn default() -> Self {
        Self {
            name: String::new(),
            inputs: Default::default(),
            instructions: Default::default(),
            outputs: Default::default(),
        }
    }
}

impl<M: Memory> Parser for Function<M> {
    type Environment = M::Environment;

    /// Parses a string into a local function.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the 'function' keyword from the string.
        let (string, _) = tag("function ")(string)?;
        // Parse the function name from the string.
        let (string, name) = recognize(pair(alpha1, many0(alt((alphanumeric1, tag("_"))))))(string)?;
        // Parse the colon ':' keyword from the string.
        let (string, _) = tag(":")(string)?;

        // Parse the inputs from the string.
        let (string, inputs) = many0(Input::parse)(string)?;
        // Parse the instructions from the string.
        let (string, instructions) = many1(Instruction::parse)(string)?;
        // Parse the outputs from the string.
        let (string, outputs) = many0(Output::parse)(string)?;

        Ok((string, Self { name: name.to_string(), inputs, instructions, outputs }))
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
