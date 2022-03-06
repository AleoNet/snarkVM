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

use crate::{instructions::Instruction, Immediate, Memory, Register};
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

pub(super) struct Local<M: Memory> {
    inputs: Vec<Register<M::Environment>>,
    instructions: Vec<Instruction<M>>,
    outputs: Vec<Register<M::Environment>>,
}

impl<M: Memory> Local<M> {
    /// Allocates a new register, stores the given input, and returns the new register.
    pub fn new_input(&mut self, input: Immediate<M::Environment>) -> Register<M::Environment> {
        match input.is_constant() {
            true => M::halt("Attempted to assign a constant value as an input"),
            false => {
                let register = M::new_register();
                self.inputs.push(register);
                M::store(&register, input);
                register
            }
        }
    }

    /// Allocates a new register, stores the given output, and returns the new register.
    pub fn new_output(&mut self) -> Register<M::Environment> {
        let register = M::new_register();
        self.outputs.push(register);
        register
    }

    /// Adds the given instruction.
    pub fn push_instruction(&mut self, instruction: Instruction<M>) {
        self.instructions.push(instruction);
    }

    /// Evaluates the function, returning the outputs.
    pub fn evaluate(&self) -> Vec<Immediate<M::Environment>> {
        for instruction in &self.instructions {
            instruction.evaluate();
        }

        let mut outputs = Vec::with_capacity(self.outputs.len());
        for output in &self.outputs {
            outputs.push(M::load(output));
        }
        outputs
    }
}

impl<M: Memory> Default for Local<M> {
    fn default() -> Self {
        Self { inputs: Default::default(), instructions: Default::default(), outputs: Default::default() }
    }
}

// impl<M: Memory> Parser for Register<M> {
//     type Environment = E;
//     type Output = Register<E>;
//
//     /// Parses a string into a register.
//     #[inline]
//     fn parse(string: &str) -> ParserResult<Self::Output> {
//         let mut newline_or_space = many0(alt((tag(" "), tag("\n"))));
//
//         // Parse the 'function' keyword from the string.
//         let (string, _) = tag("function ")(string)?;
//         // Parse the function name from the string.
//         let (string, _) = recognize(pair(alpha1, many0(alt((alphanumeric1, tag("_"))))))(string)?;
//         // Parse the colon ':' keyword from the string.
//         let (string, _) = tag(":")(string)?;
//         // Parse the whitespace from the string.
//         let (string, _) = newline_or_space(string)?;
//
//         // Parse the inputs from the string.
//
//         let (string, _) = pair(pair(tag("input "), Register::parse), x)(string)?;
//         let (string, registers) = separated_list1(tag(" "), Register::parse)(string)?;
//         let (string, _) = tag(";")(string)?;
//
//         let (string, inputs) = many0(opt(Function::parse_input_or_output))(string)?;
//         let (string, _) = newline_or_space(string)?;
//
//         // Parse the open parenthesis from the string.
//         // Parse the locator from the string.
//         let (string, locator) =
//             map_res(recognize(many1(one_of("0123456789"))), |locator: &str| locator.parse::<u64>())(string)?;
//
//         Ok((string, Register::new(locator)))
//     }
// }
//
// impl<M: Memory> fmt::Display for Register<M> {
//     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//         write!(f, "r{}", self.0)
//     }
// }
