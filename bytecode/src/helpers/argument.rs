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

use crate::Register;
use snarkvm_circuits::{Environment, Mode, Parser, ParserResult, Type};
use snarkvm_utilities::{FromBytes, ToBytes};

use core::fmt;
use nom::bytes::complete::tag;
use std::io::{Read, Result as IoResult, Write};

#[derive(Clone)]
pub struct Argument<E: Environment> {
    register: Register<E>,
    type_annotation: Type<E>,
}

impl<E: Environment> Argument<E> {
    /// Returns the register of the argument.
    pub fn register(&self) -> &Register<E> {
        &self.register
    }

    /// Returns the type annotation of the argument.
    pub fn type_annotation(&self) -> Type<E> {
        self.type_annotation
    }

    /// Returns the mode of the argument.
    pub fn mode(&self) -> &Mode {
        self.type_annotation.mode()
    }

    /// Returns `true` if the argument is a constant.
    pub fn is_constant(&self) -> bool {
        self.mode().is_constant()
    }

    /// Returns `true` if the argument is public.
    pub fn is_public(&self) -> bool {
        self.mode().is_public()
    }

    /// Returns `true` if the argument is private.
    pub fn is_private(&self) -> bool {
        self.mode().is_private()
    }
}

#[allow(clippy::let_and_return)]
impl<E: Environment> Parser for Argument<E> {
    type Environment = E;

    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "argument"
    }

    /// Parses a string into an argument.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the register from the string.
        let (string, register) = Register::parse(string)?;
        // Parse the space from the string.
        let (string, _) = tag(" ")(string)?;
        // Parse the type from the string.
        let (string, type_) = Type::parse(string)?;

        Ok((string, Self { register, type_annotation: type_ }))
    }
}

impl<E: Environment> fmt::Display for Argument<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {}", self.register(), self.type_annotation())
    }
}

impl<E: Environment> FromBytes for Argument<E> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let register = Register::<E>::read_le(&mut reader)?;
        let type_ = Type::<E>::read_le(&mut reader)?;

        Ok(Self { register, type_annotation: type_ })
    }
}

impl<E: Environment> ToBytes for Argument<E> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.register.write_le(&mut writer)?;
        self.type_annotation.write_le(&mut writer)
    }
}
