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

use crate::{Register, Value};
use snarkvm_circuits_types::prelude::*;

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

impl<E: Environment> Operand<E> {
    /// Returns the value, if the operand is a value.
    /// Returns `None` otherwise.
    ///
    /// # Examples
    /// ```ignore
    /// use snarkvm_circuits_core::{Register, Operand, Value, Literal};
    /// use snarkvm_circuits_types::environment::{Parser, Circuit};
    /// let operand = Operand::<Circuit>::Value(Value::Literal(Literal::from_str("1field.private")));
    /// assert_eq!(operand.value(), Some(&Value::Literal(Literal::from_str("1field.private"))));
    /// ```
    /// ```ignore
    /// use snarkvm_circuits_core::{Register, Operand};
    /// use snarkvm_circuits_types::environment::{Parser, Circuit};
    /// let operand = Operand::<Circuit>::Register(Register::from_str("r0"));
    /// assert_eq!(operand.value(), None);
    /// ```
    #[inline]
    pub fn value(&self) -> Option<&Value<E>> {
        match self {
            Operand::Value(value) => Some(value),
            _ => None,
        }
    }

    /// Returns the register, if the operand is a register.
    /// Returns `None` otherwise.
    ///
    /// # Examples
    /// ```
    /// use snarkvm_circuits_core::{Register, Operand};
    /// use snarkvm_circuits_types::environment::{Parser, Circuit};
    /// let operand = Operand::<Circuit>::Register(Register::from_str("r0"));
    /// assert_eq!(operand.register(), Some(&Register::from_str("r0")));
    /// ```
    /// ```
    /// use snarkvm_circuits_core::{Register, Operand, Value, Literal};
    /// use snarkvm_circuits_types::environment::{Parser, Circuit};
    /// let operand = Operand::<Circuit>::Value(Value::Literal(Literal::from_str("1field.private")));
    /// assert_eq!(operand.register(), None);
    /// ```
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
    ///
    /// # Examples
    /// ```ignore
    /// use snarkvm_circuits_core::{Register, Operand, Value, Literal};
    /// use snarkvm_circuits_types::environment::{Parser, Circuit};
    /// let operand = Operand::<Circuit>::Value(Value::Literal(Literal::from_str("1field.private")));
    /// assert_eq!(Operand::<Circuit>::parse("1field.private"), Ok(("", Operand::Value(Value::Literal(Literal::from_str("1field.private"))))));
    /// ```
    /// ```ignore
    /// use snarkvm_circuits_core::{Operand, Register};
    /// use snarkvm_circuits_types::environment::{Parser, Circuit};
    /// let operand = Operand::<Circuit>::Register(Register::from_str("r0"));
    /// assert_eq!(Operand::<Circuit>::parse("r0"), Ok(("", Operand::Register(Register::from_str("r0")))));
    /// ```
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
