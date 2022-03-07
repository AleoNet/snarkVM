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

use crate::{Argument, Immediate, Memory, Sanitizer};
use snarkvm_circuits::{Parser, ParserResult};

use core::{fmt, ops};
use nom::bytes::complete::tag;

/// Declares a function input `register` with type `annotation`.
pub struct Input<M: Memory> {
    argument: Argument<M::Environment>,
}

impl<M: Memory> Input<M> {
    /// Assigns the given immediate to the input register.
    pub(super) fn assign(&self, immediate: Immediate<M::Environment>) {
        // Retrieve the input annotations.
        let register = self.argument.register();
        let mode = self.argument.mode();
        let type_name = self.argument.type_name();

        // Ensure the type and mode are correct.
        if immediate.type_name() != type_name || &immediate.mode() != mode {
            M::halt(format!("Input register {} is not a {} {}", register, mode, type_name))
        }

        // Store the input into the register.
        M::store(register, immediate);
    }
}

impl<M: Memory> Parser for Input<M> {
    type Environment = M::Environment;

    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "input"
    }

    /// Parses a string into an input.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the input keyword from the string.
        let (string, _) = tag(Self::type_name())(string)?;
        // Parse the space from the string.
        let (string, _) = tag(" ")(string)?;
        // Parse the argument from the string.
        let (string, argument) = Argument::parse(string)?;
        // Parse the semicolon from the string.
        let (string, _) = tag(";")(string)?;

        // Initialize the input register.
        M::initialize(argument.register());

        Ok((string, Self { argument }))
    }
}

impl<M: Memory> fmt::Display for Input<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {};", Self::type_name(), self.argument)
    }
}

impl<M: Memory> ops::Deref for Input<M> {
    type Target = Argument<M::Environment>;

    fn deref(&self) -> &Self::Target {
        &self.argument
    }
}
