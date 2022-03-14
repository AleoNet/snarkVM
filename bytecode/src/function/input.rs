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
use snarkvm_circuits::{Literal, Parser, ParserResult, Type};
use snarkvm_utilities::{FromBytes, ToBytes};

use core::{fmt, ops};
use nom::bytes::complete::tag;
use once_cell::unsync::OnceCell;
use std::io::{Read, Result as IoResult, Write};

/// Declares a function input `register` with type `annotation`.
pub struct Input<M: Memory> {
    /// The register and type annotations for the input.
    argument: Argument<M::Environment>,
    /// The assigned value for this input.
    literal: OnceCell<Literal<M::Environment>>,
}

impl<M: Memory> Input<M> {
    /// Assigns the given literal to the input register.
    pub(crate) fn assign(&self, literal: Literal<M::Environment>) -> &Self {
        // Retrieve the input annotations.
        let register = self.argument.register();
        let type_ = self.argument.type_annotation();

        // Ensure the type matches.
        match Type::from(&literal) == type_ {
            // Assign the literal to this input register.
            true => match self.literal.set(literal).is_ok() {
                true => self,
                false => M::halt(format!("Input register {register} is already set")),
            },
            false => M::halt(format!("Input register {register} is not {type_}")),
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

        Ok((string, Self { argument, literal: Default::default() }))
    }

    /// Evaluates the operation in-place.
    #[inline]
    fn evaluate(&self, memory: &Self::Memory) {
        // Retrieve the input annotations.
        let register = self.argument.register();
        // Attempt to retrieve the literal this input register.
        match self.literal.get() {
            // Store the input into the register.
            Some(literal) => memory.store(register, literal.clone()),
            None => M::halt(format!("Input register {register} is not assigned yet")),
        }
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

impl<M: Memory> FromBytes for Input<M> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self { argument: Argument::read_le(&mut reader)?, literal: Default::default() })
    }
}

impl<M: Memory> ToBytes for Input<M> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.argument.write_le(&mut writer)
    }
}
