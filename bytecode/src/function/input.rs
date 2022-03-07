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

use crate::{Argument, Immediate, Memory, Operation, Sanitizer};
use snarkvm_circuits::{Environment, Parser, ParserResult};

use core::{fmt, ops};
use nom::bytes::complete::tag;
use once_cell::unsync::OnceCell;

/// Declares a function input `register` with type `annotation`.
pub struct Input<E: Environment> {
    /// The register and type annotations for the input.
    argument: Argument<E>,
    /// The assigned value for this input.
    immediate: OnceCell<Immediate<E>>,
}

impl<E: Environment> Input<E> {
    /// Assigns the given immediate to the input register.
    pub(super) fn assign<M: Memory>(&self, immediate: Immediate<E>) {
        // Retrieve the input annotations.
        let register = self.argument.register();
        let mode = self.argument.mode();
        let type_name = self.argument.type_name();

        // Ensure the type and mode are correct.
        match immediate.type_name() == type_name && &immediate.mode() == mode {
            // Assign the immediate to this input register.
            true => {
                if self.immediate.set(immediate).is_err() {
                    M::halt(format!("Input register {} is already set", register))
                }
            }
            false => M::halt(format!("Input register {} is not a {} {}", register, mode, type_name)),
        }
    }
}

impl<E: Environment> Operation<E> for Input<E> {
    /// Returns the type name as a string.
    #[inline]
    fn opcode() -> &'static str {
        "input"
    }

    /// Evaluates the operation in-place.
    fn evaluate<M: Memory<Environment = E>>(&self, memory: &M) {
        // Retrieve the input annotations.
        let register = self.argument.register();
        // Attempt to retrieve the immediate this input register.
        match self.immediate.get() {
            // Store the input into the register.
            Some(immediate) => memory.store(register, immediate.clone()),
            None => M::halt(format!("Input register {} is not set", register)),
        }
    }

    /// Parses a string into an input.
    #[inline]
    fn parse<'a, M: Memory<Environment = E>>(string: &'a str, memory: &'a mut M) -> ParserResult<'a, Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the input keyword from the string.
        let (string, _) = tag("input")(string)?;
        // Parse the space from the string.
        let (string, _) = tag(" ")(string)?;
        // Parse the argument from the string.
        let (string, argument) = Argument::parse(string)?;
        // Parse the semicolon from the string.
        let (string, _) = tag(";")(string)?;

        // Initialize the input register.
        memory.initialize(argument.register());

        Ok((string, Self { argument, immediate: Default::default() }))
    }
}

impl<E: Environment> fmt::Display for Input<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {};", Self::opcode(), self.argument)
    }
}

impl<E: Environment> ops::Deref for Input<E> {
    type Target = Argument<E>;

    fn deref(&self) -> &Self::Target {
        &self.argument
    }
}
