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
use snarkvm_circuits::{Environment, Mode, Parser, ParserResult};

use core::fmt;
use nom::{branch::alt, bytes::complete::tag, combinator::map, sequence::pair};
use snarkvm_utilities::{error, FromBytes, ToBytes};
use std::io::{Read, Result as IoResult, Write};

#[derive(Clone)]
pub enum Argument<E: Environment> {
    Boolean(Register<E>, Mode),
    Field(Register<E>, Mode),
    Group(Register<E>, Mode),
    Scalar(Register<E>, Mode),
}

impl<E: Environment> Argument<E> {
    /// Returns the register of the argument.
    pub fn register(&self) -> &Register<E> {
        match self {
            Self::Boolean(register, _) => register,
            Self::Field(register, _) => register,
            Self::Group(register, _) => register,
            Self::Scalar(register, _) => register,
        }
    }

    /// Returns the type name of the argument.
    pub fn type_name(&self) -> &'static str {
        match self {
            Self::Boolean(..) => "boolean",
            Self::Field(..) => "field",
            Self::Group(..) => "group",
            Self::Scalar(..) => "scalar",
        }
    }

    /// Returns the mode of the argument.
    pub fn mode(&self) -> &Mode {
        match self {
            Self::Boolean(_, mode) => mode,
            Self::Field(_, mode) => mode,
            Self::Group(_, mode) => mode,
            Self::Scalar(_, mode) => mode,
        }
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
        // Parse the annotation from the string.
        let result = alt((
            map(pair(pair(tag("boolean"), tag(".")), Mode::parse), |(_, mode)| Self::Boolean(register, mode)),
            map(pair(pair(tag("field"), tag(".")), Mode::parse), |(_, mode)| Self::Field(register, mode)),
            map(pair(pair(tag("group"), tag(".")), Mode::parse), |(_, mode)| Self::Group(register, mode)),
            map(pair(pair(tag("scalar"), tag(".")), Mode::parse), |(_, mode)| Self::Scalar(register, mode)),
        ))(string);
        result
    }
}

impl<E: Environment> fmt::Display for Argument<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {}.{}", self.register(), self.type_name(), self.mode())
    }
}

impl<E: Environment> FromBytes for Argument<E> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self>
    where
        Self: Sized,
    {
        match u8::read_le(&mut reader) {
            Ok(i) if i == Self::Boolean as u8 => {
                Ok(Self::Boolean(Register::<E>::read_le(&mut reader)?, Mode::read_le(&mut reader)?))
            }
            Ok(i) if i == Self::Field as u8 => {
                Ok(Self::Field(Register::<E>::read_le(&mut reader)?, Mode::read_le(&mut reader)?))
            }
            Ok(i) if i == Self::Group as u8 => {
                Ok(Self::Group(Register::<E>::read_le(&mut reader)?, Mode::read_le(&mut reader)?))
            }
            Ok(i) if i == Self::Scalar as u8 => {
                Ok(Self::Scalar(Register::<E>::read_le(&mut reader)?, Mode::read_le(&mut reader)?))
            }
            Ok(_) => Err(error("FromBytes::read failed for Argument")),
            Err(err) => Err(err),
        }
    }
}

impl<E: Environment> ToBytes for Argument<E> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()>
    where
        Self: Sized,
    {
        match self {
            Self::Boolean(register, mode) => {
                u8::write_le(&(Self::Boolean as u8), &mut writer)?;
                register.write_le(&mut writer)?;
                mode.write_le(&mut writer)
            }
            Self::Field(register, mode) => {
                u8::write_le(&(Self::Field as u8), &mut writer)?;
                register.write_le(&mut writer)?;
                mode.write_le(&mut writer)
            }
            Self::Group(register, mode) => {
                u8::write_le(&(Self::Group as u8), &mut writer)?;
                register.write_le(&mut writer)?;
                mode.write_le(&mut writer)
            }
            Self::Scalar(register, mode) => {
                u8::write_le(&(Self::Scalar as u8), &mut writer)?;
                register.write_le(&mut writer)?;
                mode.write_le(&mut writer)
            }
        }
    }
}
