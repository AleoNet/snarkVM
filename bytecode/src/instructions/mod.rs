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

pub mod add;
pub use add::*;

pub mod store;
pub use store::*;

pub mod sub;
pub use sub::*;

use crate::{Memory, Operation, Sanitizer};
use snarkvm_circuits::{Parser, ParserResult};

use core::fmt;
use nom::{
    branch::alt,
    bytes::complete::tag,
    combinator::map,
    sequence::{pair, preceded},
};

pub enum Instruction<M: Memory> {
    /// Adds `first` with `second`, storing the outcome in `destination`.
    Add(Add<M>),
    /// Stores `operand` into `register`, if `destination` is not already set.
    Store(Store<M>),
    /// Subtracts `first` from `second`, storing the outcome in `destination`.
    Sub(Sub<M>),
}

impl<M: Memory> Instruction<M> {
    /// Returns the opcode of the instruction.
    pub fn opcode(&self) -> &'static str {
        match self {
            Self::Add(..) => "add",
            Self::Store(..) => "store",
            Self::Sub(..) => "sub",
        }
    }

    /// Evaluates the instruction.
    pub fn evaluate(&self) {
        match self {
            Self::Add(instruction) => instruction.evaluate(),
            Self::Store(instruction) => instruction.evaluate(),
            Self::Sub(instruction) => instruction.evaluate(),
        }
    }
}

impl<M: Memory> Parser for Instruction<M> {
    type Environment = M::Environment;

    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "instruction"
    }

    /// Parses a string into an instruction.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the instruction from the string.
        let (string, instruction) = alt((
            // Note that order of the individual parsers matters.
            preceded(pair(tag(Add::<M>::type_name()), tag(" ")), map(Add::parse, |operation| operation.into())),
            preceded(pair(tag(Store::<M>::type_name()), tag(" ")), map(Store::parse, |operation| operation.into())),
            preceded(pair(tag(Sub::<M>::type_name()), tag(" ")), map(Sub::parse, |operation| operation.into())),
        ))(string)?;
        // Parse the semicolon from the string.
        let (string, _) = tag(";")(string)?;

        Ok((string, instruction))
    }
}

impl<M: Memory> fmt::Display for Instruction<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Add(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::Store(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::Sub(instruction) => write!(f, "{} {};", self.opcode(), instruction),
        }
    }
}
