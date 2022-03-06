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

use crate::{Argument, Memory, Operation, Sanitizer};
use snarkvm_circuits::{Parser, ParserResult};

use core::{fmt, ops};
use nom::bytes::complete::tag;

/// Declares a `register` as a function output with type `annotation`.
pub struct Output<M: Memory> {
    argument: Argument<M::Environment>,
}

impl<M: Memory> Operation for Output<M> {
    type Memory = M;

    /// Evaluates the operation in-place.
    fn evaluate(&self) {
        // Retrieve the output annotations.
        let register = self.argument.register();
        let mode = self.argument.mode();
        let type_name = self.argument.type_name();

        // Load the output from memory.
        let immediate = M::load(register);

        // Ensure the type and mode are correct.
        if immediate.type_name() != type_name || &immediate.mode() != mode {
            M::halt(format!("Output register {} is not a {} {}", register, mode, type_name))
        }
    }
}

impl<M: Memory> Parser for Output<M> {
    type Environment = M::Environment;

    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "output"
    }

    /// Parses a string into an output.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the output keyword from the string.
        let (string, _) = tag(Self::type_name())(string)?;
        // Parse the space from the string.
        let (string, _) = tag(" ")(string)?;
        // Parse the argument from the string.
        let (string, argument) = Argument::parse(string)?;
        // Parse the semicolon from the string.
        let (string, _) = tag(";")(string)?;

        // Ensure the output register exists.
        match M::exists(argument.register()) {
            true => Ok((string, Self { argument })),
            false => M::halt(format!("Tried to set non-existent register {} as an output", argument.register())),
        }
    }
}

impl<M: Memory> fmt::Display for Output<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {};", Self::type_name(), self.argument)
    }
}

impl<M: Memory> ops::Deref for Output<M> {
    type Target = Argument<M::Environment>;

    fn deref(&self) -> &Self::Target {
        &self.argument
    }
}
