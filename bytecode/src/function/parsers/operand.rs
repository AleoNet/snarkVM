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

use crate::{helpers::Register, Program, Value};
use snarkvm_circuits::prelude::*;
use snarkvm_utilities::{error, FromBytes, ToBytes};

use core::fmt;
use std::io::{Read, Result as IoResult, Write};

/// The operand enum represents the complete set of options for operands in an instruction.
/// This enum is designed to support instructions (such as `add {Register} {Value} into {Register}`).
#[derive(Clone, Debug)]
pub enum Operand<P: Program> {
    /// A value contains a declared literal or composite.
    Value(Value<P>),
    /// A register contains its locator in memory.
    Register(Register<P>),
}

impl<P: Program> From<&Self> for Operand<P> {
    /// Initializes a new operand from a reference to an operand.
    #[inline]
    fn from(operand: &Self) -> Self {
        match operand {
            Operand::Value(value) => Operand::Value(value.clone()),
            Operand::Register(register) => Operand::Register(register.clone()),
        }
    }
}

impl<P: Program> From<Register<P>> for Operand<P> {
    /// Initializes a new operand from a register.
    #[inline]
    fn from(register: Register<P>) -> Self {
        Operand::Register(register)
    }
}

impl<P: Program> From<&Register<P>> for Operand<P> {
    /// Initializes a new operand from a reference to a register.
    #[inline]
    fn from(register: &Register<P>) -> Self {
        Operand::Register(register.clone())
    }
}

impl<P: Program> From<Value<P>> for Operand<P> {
    /// Initializes a new operand from a value.
    #[inline]
    fn from(value: Value<P>) -> Self {
        Operand::Value(value)
    }
}

impl<P: Program> From<&Value<P>> for Operand<P> {
    /// Initializes a new operand from a reference to a value.
    #[inline]
    fn from(value: &Value<P>) -> Self {
        Operand::Value(value.clone())
    }
}

impl<P: Program> Operand<P> {
    /// Returns the value, if the operand is a value.
    /// Returns `None` otherwise.
    #[inline]
    pub fn value(&self) -> Option<&Value<P>> {
        match self {
            Operand::Value(value) => Some(value),
            _ => None,
        }
    }

    /// Returns the register, if the operand is a register.
    /// Returns `None` otherwise.
    #[inline]
    pub fn register(&self) -> Option<&Register<P>> {
        match self {
            Operand::Register(register) => Some(register),
            _ => None,
        }
    }

    /// Returns `true` if the operand is a value.
    /// Returns `false` if the operand is a register.
    #[inline]
    pub fn is_value(&self) -> bool {
        matches!(self, Operand::Value(_))
    }

    /// Returns `true` if the operand is a register.
    /// Returns `false` if the operand is a value.
    #[inline]
    pub fn is_register(&self) -> bool {
        matches!(self, Operand::Register(_))
    }
}

impl<P: Program> Parser for Operand<P> {
    type Environment = E;

    /// Parses a string into a operand.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse to determine the operand (order matters).
        alt((map(Value::parse, |value| Self::Value(value)), map(Register::parse, |register| Self::Register(register))))(
            string,
        )
    }
}

impl<P: Program> fmt::Display for Operand<P> {
    /// Prints the operand as a string.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            // Prints the value, i.e. 10field.private
            Self::Value(literal) => fmt::Display::fmt(literal, f),
            // Prints the register, i.e. r0 or r0.owner
            Self::Register(register) => fmt::Display::fmt(register, f),
        }
    }
}

impl<P: Program> FromBytes for Operand<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        match u8::read_le(&mut reader) {
            Ok(0) => Ok(Self::Value(Value::read_le(&mut reader)?)),
            Ok(1) => Ok(Self::Register(Register::read_le(&mut reader)?)),
            Ok(variant) => Err(error(format!("Failed to deserialize operand variant {variant}"))),
            Err(err) => Err(err),
        }
    }
}

impl<P: Program> ToBytes for Operand<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        match self {
            Self::Value(value) => {
                u8::write_le(&0u8, &mut writer)?;
                value.write_le(&mut writer)
            }
            Self::Register(register) => {
                u8::write_le(&1u8, &mut writer)?;
                register.write_le(&mut writer)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Process, Register, Value};
    use snarkvm_circuits::{environment::Parser, Literal};

    type P = Process;

    #[test]
    fn test_operand_value() {
        let operand = Operand::<P>::Value(Value::Literal(Literal::from_str("1field.private")));
        assert_eq!(operand.value(), Some(&Value::Literal(Literal::from_str("1field.private"))));
        assert_eq!(operand.register(), None);
        assert!(operand.is_value());
        assert!(!operand.is_register());
    }

    #[test]
    fn test_operand_register() {
        let operand = Operand::<P>::Register(Register::from_str("r0"));
        assert_eq!(operand.value(), None);
        assert_eq!(operand.register(), Some(&Register::from_str("r0")));
        assert!(!operand.is_value());
        assert!(operand.is_register());
    }

    #[test]
    fn test_operand_register_member() {
        let operand = Operand::<P>::Register(Register::from_str("r0.owner"));
        assert_eq!(operand.value(), None);
        assert_eq!(operand.register(), Some(&Register::from_str("r0.owner")));
        assert!(!operand.is_value());
        assert!(operand.is_register());
    }

    #[test]
    fn test_operand_parse() {
        let operand = Operand::<P>::parse("1field.private").unwrap().1;
        assert_eq!(operand.value(), Some(&Value::Literal(Literal::from_str("1field.private"))));
        assert_eq!(operand.register(), None);
        assert!(operand.is_value());
        assert!(!operand.is_register());

        let operand = Operand::<P>::parse("r0").unwrap().1;
        assert_eq!(operand.value(), None);
        assert_eq!(operand.register(), Some(&Register::from_str("r0")));
        assert!(!operand.is_value());
        assert!(operand.is_register());

        let operand = Operand::<P>::parse("r0.owner").unwrap().1;
        assert_eq!(operand.value(), None);
        assert_eq!(operand.register(), Some(&Register::from_str("r0.owner")));
        assert!(!operand.is_value());
        assert!(operand.is_register());
    }

    #[test]
    fn test_operand_display() {
        let operand = Operand::<P>::parse("1field.private").unwrap().1;
        assert_eq!(format!("{operand}"), "1field.private");

        let operand = Operand::<P>::parse("r0").unwrap().1;
        assert_eq!(format!("{operand}"), "r0");

        let operand = Operand::<P>::parse("r0.owner").unwrap().1;
        assert_eq!(format!("{operand}"), "r0.owner");
    }
}
