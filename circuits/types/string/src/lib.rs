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

#![forbid(unsafe_code)]

pub mod from_bits;
pub mod to_bits;
pub mod to_fields;

#[cfg(test)]
use snarkvm_circuits_environment::assert_scope;

use snarkvm_circuits_environment::{prelude::*, string_parser::parse_string};
use snarkvm_circuits_types_boolean::Boolean;
use snarkvm_circuits_types_integers::U8;

#[derive(Clone)]
pub struct StringType<E: Environment> {
    mode: Mode,
    bytes: Vec<U8<E>>,
}

impl<E: Environment> StringTrait for StringType<E> {}

impl<E: Environment> Inject for StringType<E> {
    type Primitive = String;

    /// Initializes a new instance of a string.
    fn new(mode: Mode, string: String) -> Self {
        // Ensure the string is within the allowed capacity.
        let num_bytes = string.len();
        match num_bytes <= E::NUM_STRING_BYTES as usize {
            true => Self { mode, bytes: string.as_bytes().iter().map(|byte| U8::new(mode, *byte)).collect() },
            false => E::halt(format!("Attempted to allocate a string of size {num_bytes}")),
        }
    }
}

impl<E: Environment> Eject for StringType<E> {
    type Primitive = String;

    ///
    /// Ejects the mode of the string.
    ///
    fn eject_mode(&self) -> Mode {
        match self.bytes.is_empty() {
            true => self.mode,
            false => self.bytes.eject_mode(),
        }
    }

    ///
    /// Ejects the string as a string literal.
    ///
    fn eject_value(&self) -> Self::Primitive {
        // Ensure the string is within the allowed capacity.
        let num_bytes = self.bytes.len();
        match num_bytes <= E::NUM_STRING_BYTES as usize {
            true => String::from_utf8(self.bytes.eject_value())
                .unwrap_or_else(|error| E::halt(&format!("Failed to eject a string value: {error}"))),
            false => E::halt(format!("Attempted to eject a string of size {num_bytes}")),
        }
    }
}

impl<E: Environment> Parser for StringType<E> {
    type Environment = E;

    /// Parses a string into a string circuit.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the starting quote '"' keyword from the string.
        let (string, value) = parse_string(string)?;
        // Parse the mode from the string.
        let (string, mode) = opt(pair(tag("."), Mode::parse))(string)?;

        match mode {
            Some((_, mode)) => Ok((string, StringType::new(mode, value))),
            None => Ok((string, StringType::new(Mode::Constant, value))),
        }
    }
}

impl<E: Environment> TypeName for StringType<E> {
    /// Returns the type name of the circuit as a string.
    #[inline]
    fn type_name() -> &'static str {
        "string"
    }
}

impl<E: Environment> fmt::Debug for StringType<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "\"{}\"", self.eject_value())
    }
}

impl<E: Environment> fmt::Display for StringType<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "\"{}\".{}", self.eject_value(), self.eject_mode())
    }
}
