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

use core::fmt;
use nom::bytes::complete::tag;

/// Declares a function input `register` with type `annotation`.
pub struct Input<M: Memory> {
    // parser: Box<dyn Parser<Environment = M::Environment>>,
    argument: Argument<M::Environment>,
}

impl<M: Memory> Operation for Input<M> {
    type Memory = M;

    const OPCODE: &'static str = "input";

    /// Evaluates the operation in-place.
    fn evaluate(&self) {
        // Loads the input from memory, and stores it into the register.
        M::store(self.argument.register(), M::load_input(&self.argument))
    }
}

impl<M: Memory> Parser for Input<M> {
    type Environment = M::Environment;

    /// Parses a string into an input.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the input keyword from the string.
        let (string, _) = tag(Self::OPCODE)(string)?;
        // Parse the space from the string.
        let (string, _) = tag(" ")(string)?;
        // Parse the argument from the string.
        let (string, argument) = Argument::parse(string)?;
        // Parse the semicolon from the string.
        let (string, _) = tag(";")(string)?;

        Ok((string, Self { argument }))
    }
}

impl<M: Memory> fmt::Display for Input<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {};", Self::OPCODE, self.argument)
    }
}
