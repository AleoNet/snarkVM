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

use crate::{instructions::Instruction, Immediate, Memory, Operation, Register, Sanitizer};
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
    /// The function name.
    name: String,
    /// The function arguments provided by the caller.
    arguments: Vec<Register<M::Environment>>,
    /// The instructions to initialize the function inputs.
    inputs: Vec<Input<M>>,
    /// The main instructions of the function.
    instructions: Vec<Instruction<M>>,
    /// The instructions to initialize the function outputs.
    outputs: Vec<Output<M>>,
}

impl<M: Memory> Function<M> {
    /// Allocates the given inputs, by appending them as function inputs.
    pub fn add_inputs(&mut self, inputs: &[Immediate<M::Environment>]) -> &mut Self {
        // Append new inputs from the index of the last assigned input.
        for (input, immediate) in (self.inputs.iter().skip(self.arguments.len())).zip(inputs) {
            // Store the immediate into the input register.
            input.assign(immediate.clone());
            // Save the input register.
            self.arguments.push(*(*input).register());
        }
        self
    }

    /// Evaluates the function, returning the outputs.
    pub fn evaluate(&mut self, inputs: &[Immediate<M::Environment>]) -> Vec<Immediate<M::Environment>> {
        self.add_inputs(inputs);
        self.instructions.iter().for_each(Instruction::evaluate);
        self.outputs.iter().for_each(Operation::evaluate);
        self.outputs()
    }

    /// Returns the outputs from the function.
    pub(super) fn outputs(&self) -> Vec<Immediate<M::Environment>> {
        self.outputs.iter().map(|output| M::load((*output).register())).collect()
    }

    /// Returns the number of arguments provided by the caller.
    pub fn num_arguments(&self) -> u64 {
        self.arguments.len() as u64
    }

    /// Returns the number of inputs for the function.
    pub fn num_inputs(&self) -> u64 {
        self.inputs.len() as u64
    }

    /// Returns the number of outputs for the function.
    pub fn num_outputs(&self) -> u64 {
        self.outputs.len() as u64
    }
}

impl<M: Memory> Parser for Function<M> {
    type Environment = M::Environment;

    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "function"
    }

    /// Parses a string into a local function.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the 'function' keyword from the string.
        let (string, _) = tag(Self::type_name())(string)?;
        // Parse the space from the string.
        let (string, _) = tag(" ")(string)?;
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

        Ok((string, Self { name: name.to_string(), arguments: Default::default(), inputs, instructions, outputs }))
    }
}

impl<M: Memory> fmt::Display for Function<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut output = format!("{} {}:\n", Self::type_name(), self.name);
        for instruction in &self.instructions {
            output += &format!("    {}", instruction);
        }
        write!(f, "{}", output)
    }
}
