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
use snarkvm_utilities::{FromBytes, ToBytes};
use std::io::{Read, Result as IoResult, Write};

/// Declares a `register` as a function output with type `annotation`.
pub struct Output<M: Memory> {
    argument: Argument<M::Environment>,
}

impl<M: Memory> Operation for Output<M> {
    type Memory = M;

    /// Returns the type name as a string.
    #[inline]
    fn opcode() -> &'static str {
        "output"
    }

    /// Evaluates the operation in-place.
    #[inline]
    fn evaluate(&self, memory: &Self::Memory) {
        // Retrieve the output annotations.
        let register = self.argument.register();
        let mode = self.argument.mode();
        let type_name = self.argument.type_name();

        // Load the output from memory.
        let immediate = memory.load(register);

        // Ensure the type and mode are correct.
        if immediate.type_name() != type_name || &immediate.mode() != mode {
            M::halt(format!("Output register {} is not a {} {}", register, mode, type_name))
        }
    }

    /// Parses a string into an output.
    #[inline]
    fn parse(string: &str, memory: Self::Memory) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the output keyword from the string.
        let (string, _) = tag("output")(string)?;
        // Parse the space from the string.
        let (string, _) = tag(" ")(string)?;
        // Parse the argument from the string.
        let (string, argument) = Argument::parse(string)?;
        // Parse the semicolon from the string.
        let (string, _) = tag(";")(string)?;

        // Ensure the output register exists.
        match memory.exists(argument.register()) {
            true => Ok((string, Self { argument })),
            false => M::halt(format!("Tried to set non-existent register {} as an output", argument.register())),
        }
    }
}

impl<M: Memory> fmt::Display for Output<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {};", Self::opcode(), self.argument)
    }
}

impl<M: Memory> ops::Deref for Output<M> {
    type Target = Argument<M::Environment>;

    fn deref(&self) -> &Self::Target {
        &self.argument
    }
}

impl<M: Memory> FromBytes for Output<M> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self>
    where
        Self: Sized,
    {
        let argument = Argument::read_le(&mut reader)?;
        Ok(Self { argument })
    }
}

impl<M: Memory> ToBytes for Output<M> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()>
    where
        Self: Sized,
    {
        self.argument.write_le(&mut writer)
    }
}
