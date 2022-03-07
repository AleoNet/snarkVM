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
use snarkvm_circuits::{Parser, ParserResult};

use core::{fmt, ops};
use nom::bytes::complete::tag;
use once_cell::unsync::OnceCell;

/// Declares a function input `register` with type `annotation`.
pub struct Input<M: Memory> {
    /// The register and type annotations for the input.
    argument: Argument<M::Environment>,
    /// The assigned value for this input.
    immediate: OnceCell<Immediate<M::Environment>>,
}

impl<M: Memory> Input<M> {
    /// Assigns the given immediate to the input register.
    pub(super) fn assign(&self, immediate: Immediate<M::Environment>) {
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

impl<M: Memory> Operation for Input<M> {
    type Memory = M;

    /// Returns the type name as a string.
    #[inline]
    fn opcode() -> &'static str {
        "input"
    }

    /// Evaluates the operation in-place.
    #[inline]
    fn evaluate(&self, memory: &Self::Memory) {
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
    fn parse(string: &str, memory: Self::Memory) -> ParserResult<Self> {
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

impl<M: Memory> fmt::Display for Input<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {};", Self::opcode(), self.argument)
    }
}

impl<M: Memory> ops::Deref for Input<M> {
    type Target = Argument<M::Environment>;

    fn deref(&self) -> &Self::Target {
        &self.argument
    }
}
