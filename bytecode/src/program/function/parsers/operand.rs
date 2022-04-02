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

use crate::program::{helpers::Register, Value};
use snarkvm_circuits::prelude::*;

use core::fmt;

/// The operand enum represents the complete set of options for operands in an instruction.
/// This enum is designed to support instructions (such as `add {Register} {Value} into {Register}`).
#[derive(Clone, Debug)]
pub enum Operand<E: Environment> {
    /// A value contains a declared literal or composite.
    Value(Value<E>),
    /// A register contains its locator in memory.
    Register(Register<E>),
}

impl<E: Environment> From<&Self> for Operand<E> {
    /// Initializes a new operand from a reference to an operand.
    #[inline]
    fn from(operand: &Self) -> Self {
        match operand {
            Operand::Value(value) => Operand::Value(value.clone()),
            Operand::Register(register) => Operand::Register(register.clone()),
        }
    }
}

impl<E: Environment> From<Register<E>> for Operand<E> {
    /// Initializes a new operand from a register.
    #[inline]
    fn from(register: Register<E>) -> Self {
        Operand::Register(register)
    }
}

impl<E: Environment> From<&Register<E>> for Operand<E> {
    /// Initializes a new operand from a reference to a register.
    #[inline]
    fn from(register: &Register<E>) -> Self {
        Operand::Register(register.clone())
    }
}

impl<E: Environment> From<Value<E>> for Operand<E> {
    /// Initializes a new operand from a value.
    #[inline]
    fn from(value: Value<E>) -> Self {
        Operand::Value(value)
    }
}

impl<E: Environment> From<&Value<E>> for Operand<E> {
    /// Initializes a new operand from a reference to a value.
    #[inline]
    fn from(value: &Value<E>) -> Self {
        Operand::Value(value.clone())
    }
}

impl<E: Environment> Operand<E> {
    /// Returns the value, if the operand is a value.
    /// Returns `None` otherwise.
    #[inline]
    pub fn value(&self) -> Option<&Value<E>> {
        match self {
            Operand::Value(value) => Some(value),
            _ => None,
        }
    }

    /// Returns the register, if the operand is a register.
    /// Returns `None` otherwise.
    #[inline]
    pub fn register(&self) -> Option<&Register<E>> {
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

impl<E: Environment> Parser for Operand<E> {
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

impl<E: Environment> fmt::Display for Operand<E> {
    /// Prints the operand as a string.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            // Prints the value, i.e. 10field.private
            Self::Value(literal) => literal.fmt(f),
            // Prints the register, i.e. r0 or r0.owner
            Self::Register(register) => register.fmt(f),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::program::{Register, Value};
    use snarkvm_circuits::{
        environment::{Circuit, Parser},
        Literal,
    };

    type E = Circuit;

    #[test]
    fn test_operand_value() {
        let operand = Operand::<E>::Value(Value::Literal(Literal::from_str("1field.private")));
        // assert_eq!(operand.value(), Some(&Value::Literal(Literal::from_str("1field.private"))));
        assert_eq!(operand.register(), None);
        assert!(operand.is_value());
        assert!(!operand.is_register());
    }

    #[test]
    fn test_operand_register() {
        let operand = Operand::<E>::Register(Register::from_str("r0"));
        // assert_eq!(operand.value(), None);
        assert_eq!(operand.register(), Some(&Register::from_str("r0")));
        assert!(!operand.is_value());
        assert!(operand.is_register());
    }

    #[test]
    fn test_operand_register_member() {
        let operand = Operand::<E>::Register(Register::from_str("r0.owner"));
        // assert_eq!(operand.value(), None);
        assert_eq!(operand.register(), Some(&Register::from_str("r0.owner")));
        assert!(!operand.is_value());
        assert!(operand.is_register());
    }

    #[test]
    fn test_operand_parse() {
        let operand = Operand::<E>::parse("1field.private").unwrap().1;
        // assert_eq!(operand.value(), Some(&Value::Literal(Literal::from_str("1field.private"))));
        assert_eq!(operand.register(), None);
        assert!(operand.is_value());
        assert!(!operand.is_register());

        let operand = Operand::<E>::parse("r0").unwrap().1;
        // assert_eq!(operand.value(), None);
        assert_eq!(operand.register(), Some(&Register::from_str("r0")));
        assert!(!operand.is_value());
        assert!(operand.is_register());

        let operand = Operand::<E>::parse("r0.owner").unwrap().1;
        // assert_eq!(operand.value(), None);
        assert_eq!(operand.register(), Some(&Register::from_str("r0.owner")));
        assert!(!operand.is_value());
        assert!(operand.is_register());
    }

    #[test]
    fn test_operand_display() {
        let operand = Operand::<E>::parse("1field.private").unwrap().1;
        assert_eq!(format!("{operand}"), "1field.private");

        let operand = Operand::<E>::parse("r0").unwrap().1;
        assert_eq!(format!("{operand}"), "r0");

        let operand = Operand::<E>::parse("r0.owner").unwrap().1;
        assert_eq!(format!("{operand}"), "r0.owner");
    }
}
