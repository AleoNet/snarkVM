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
use once_cell::unsync::OnceCell;
use nom::{
    branch::alt,
    bytes::complete::tag,
    sequence::pair,
    character::complete::{alpha1, alphanumeric1},
    combinator::{opt, recognize},
    multi::{many0, many1, separated_list0, separated_list1},
};

pub(super) struct Input<M: Memory> {
    inputs: Vec<Register<M::Environment>>,
    register: OnceCell<Register<M::Environment>>,
}

impl<M: Memory> Input<M> {
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

    /// Returns `true` if the given register is already set.
    pub(super) fn is_set(&self, register: &Register<E>) -> bool {
        // Attempt to retrieve the specified register from memory.
        match self.registers.get(register) {
            // Check if the register is set.
            Some(memory) => memory.get().is_some(),
            None => false,
        }
    }

    /// Attempts to load the value from the register.
    pub(super) fn load(&self, register: &Register<E>) -> Immediate<E> {
        // Attempt to retrieve the specified register from memory.
        let memory = match self.registers.get(register) {
            Some(memory) => memory,
            None => E::halt(format!("Register {} does not exist", register)),
        };

        // Attempt to retrieve the value the specified register.
        match memory.get() {
            Some(value) => value.clone(),
            None => E::halt(format!("Register {} is not set", register)),
        }
    }

    /// Attempts to store value into the register.
    pub(super) fn store(&self, register: &Register<E>, value: Immediate<E>) {
        // Attempt to retrieve the specified register from memory.
        let memory = match self.registers.get(register) {
            Some(memory) => memory,
            None => E::halt(format!("Register {} does not exist", register)),
        };

        // Attempt to set the specified register with the given value.
        if memory.set(value).is_err() {
            E::halt(format!("Register {} is already set", register))
        }
    }
}

impl<M: Memory> Parser for Input<M> {
    type Environment = E;
    type Output = Input<M>;

    /// Parses a string into a register.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self::Output> {
        let mut newline_or_space = many0(alt((tag(" "), tag("\n"))));

        // Parse the inputs from the string.

        let (string, _) = pair(pair(tag("input "), Register::parse), x)(string)?;
        let (string, registers) = separated_list1(tag(" "), Register::parse)(string)?;
        let (string, _) = tag(";")(string)?;

        let (string, inputs) = many0(opt(Function::parse_input_or_output))(string)?;
        let (string, _) = newline_or_space(string)?;

        // Parse the open parenthesis from the string.
        // Parse the locator from the string.
        let (string, locator) =
            map_res(recognize(many1(one_of("0123456789"))), |locator: &str| locator.parse::<u64>())(string)?;

        Ok((string, Register::new(locator)))
    }
}

impl<M: Memory> fmt::Display for Input<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "r{}", self.0)
    }
}
