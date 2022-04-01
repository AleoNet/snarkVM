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

pub mod sub;
pub use sub::*;

use crate::{functions::parsers::Operand, helpers::Register, Function, Literal, Sanitizer};
use snarkvm_circuits_types::environment::{Environment, Parser, ParserResult};
use snarkvm_utilities::{error, FromBytes, ToBytes};

use core::fmt;
use nom::{
    branch::alt,
    bytes::complete::tag,
    combinator::map,
    sequence::{pair, preceded},
};
use std::io::{Read, Result as IoResult, Write};

pub trait Opcode {
    ///
    /// Returns the opcode of the operation.
    ///
    fn opcode() -> &'static str;
}

// pub trait Operation: Parser + Into<Instruction<Self::Memory>> {
pub trait Operation<E: Environment> {
    ///
    /// Evaluates the operation.
    ///
    fn evaluate(&self, function: &mut Function<E>);
}

pub enum Instruction<E: Environment> {
    /// Adds `first` with `second`, storing the outcome in `destination`.
    Add(Add<E>),
    /// Subtracts `first` from `second`, storing the outcome in `destination`.
    Sub(Sub<E>),
}

impl<E: Environment> Instruction<E> {
    /// Returns the opcode of the instruction.
    #[inline]
    pub(crate) fn opcode(&self) -> &'static str {
        match self {
            Self::Add(..) => Add::<E>::opcode(),
            Self::Sub(..) => Sub::<E>::opcode(),
        }
    }

    /// Returns the operands of the instruction.
    #[inline]
    pub(crate) fn operands(&self) -> Vec<Operand<E>> {
        match self {
            Self::Add(add) => add.operands(),
            Self::Sub(sub) => sub.operands(),
        }
    }

    /// Returns the destination register of the instruction.
    #[inline]
    pub(crate) fn destination(&self) -> &Register<E> {
        match self {
            Self::Add(add) => add.destination(),
            Self::Sub(sub) => sub.destination(),
        }
    }

    /// Evaluates the instruction.
    #[inline]
    pub(crate) fn evaluate(&self, function: &mut Function<E>) {
        match self {
            Self::Add(instruction) => instruction.evaluate(function),
            Self::Sub(instruction) => instruction.evaluate(function),
        }
    }
}

impl<E: Environment> Parser for Instruction<E> {
    type Environment = E;

    /// Parses a string into an instruction.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the instruction from the string.
        let (string, instruction) = alt((
            // Note that order of the individual parsers matters.
            preceded(pair(tag(Add::<E>::opcode()), tag(" ")), map(Add::parse, Into::into)),
            preceded(pair(tag(Sub::<E>::opcode()), tag(" ")), map(Sub::parse, Into::into)),
        ))(string)?;
        // Parse the semicolon from the string.
        let (string, _) = tag(";")(string)?;

        Ok((string, instruction))
    }
}

impl<E: Environment> fmt::Display for Instruction<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Add(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::Sub(instruction) => write!(f, "{} {};", self.opcode(), instruction),
        }
    }
}

// impl<E: Environment> FromBytes for Instruction<E> {
//     fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
//         match u16::read_le(&mut reader) {
//             Ok(0) => Ok(Self::Add(Add::read_le(&mut reader)?)),
//             Ok(1) => Ok(Self::Sub(Sub::read_le(&mut reader)?)),
//             Ok(code) => Err(error(format!("FromBytes failed to parse an instruction of code {code}"))),
//             Err(err) => Err(err),
//         }
//     }
// }
//
// impl<E: Environment> ToBytes for Instruction<E> {
//     fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
//         match self {
//             Self::Add(instruction) => {
//                 u16::write_le(&0u16, &mut writer)?;
//                 instruction.write_le(&mut writer)
//             }
//             Self::Sub(instruction) => {
//                 u16::write_le(&1u16, &mut writer)?;
//                 instruction.write_le(&mut writer)
//             }
//         }
//     }
// }
