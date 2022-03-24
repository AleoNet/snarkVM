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

use crate::{Memory, Register};
use snarkvm_circuits::{Environment, Literal, Mode, Parser, ParserResult};
use snarkvm_utilities::{error, FromBytes, ToBytes};

use core::fmt;
use nom::{branch::alt, combinator::map};
use std::io::{Read, Result as IoResult, Write};

#[derive(Clone)]
pub enum Operand<E: Environment> {
    Literal(Literal<E>),
    Register(Register<E>),
}

impl<E: Environment> Operand<E> {
    /// Returns `true` if the value type is an literal.
    pub fn is_literal(&self) -> bool {
        matches!(self, Self::Literal(..))
    }

    /// Returns `true` if the value type is a register.
    pub fn is_register(&self) -> bool {
        matches!(self, Self::Register(..))
    }

    /// Returns the literal from a register, otherwise passes the stored literal through.
    pub(crate) fn load<M: Memory<Environment = E>>(&self, memory: &M) -> Literal<M::Environment> {
        match self {
            Self::Literal(literal) => literal.clone(),
            Self::Register(register) => memory.load(register),
        }
    }
}

impl<E: Environment> From<Literal<E>> for Operand<E> {
    /// Ensures that the given literal is a constant.
    fn from(literal: Literal<E>) -> Operand<E> {
        match literal.mode() {
            Mode::Constant => Operand::Literal(literal),
            mode => E::halt(format!("Attempted to assign a {} literal", mode)),
        }
    }
}

impl<E: Environment> From<&Literal<E>> for Operand<E> {
    /// Ensures that the given literal is a constant.
    fn from(literal: &Literal<E>) -> Operand<E> {
        Operand::from(literal.clone())
    }
}

impl<E: Environment> From<Register<E>> for Operand<E> {
    fn from(register: Register<E>) -> Operand<E> {
        Operand::Register(register)
    }
}

impl<E: Environment> From<&Register<E>> for Operand<E> {
    fn from(register: &Register<E>) -> Operand<E> {
        Operand::from(*register)
    }
}

impl<E: Environment> Parser for Operand<E> {
    type Environment = E;

    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "operand"
    }

    /// Parses a string into an operand.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        alt((
            map(Literal::parse, |literal| Self::Literal(literal)),
            map(Register::parse, |register| Self::Register(register)),
        ))(string)
    }
}

impl<E: Environment> fmt::Display for Operand<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Literal(literal) => literal.fmt(f),
            Self::Register(register) => register.fmt(f),
        }
    }
}

impl<E: Environment> FromBytes for Operand<E> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        match u8::read_le(&mut reader) {
            Ok(0) => Ok(Self::Literal(Literal::read_le(&mut reader)?)),
            Ok(1) => Ok(Self::Register(Register::read_le(&mut reader)?)),
            Ok(variant) => Err(error(format!("FromBytes failed to parse an operand of variant {variant}"))),
            Err(err) => Err(err),
        }
    }
}

impl<E: Environment> ToBytes for Operand<E> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        match self {
            Self::Literal(literal) => {
                u8::write_le(&0u8, &mut writer)?;
                literal.write_le(&mut writer)
            }
            Self::Register(register) => {
                u8::write_le(&1u8, &mut writer)?;
                register.write_le(&mut writer)
            }
        }
    }
}
