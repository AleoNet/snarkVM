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

use snarkvm_circuits_types::prelude::*;

use once_cell::unsync::OnceCell;
use std::collections::HashMap;

use snarkvm_utilities::{error, FromBytes, ToBytes};

use core::fmt;
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alpha1, alphanumeric1},
    combinator::{map, map_res, recognize},
    multi::{many0, many1},
    sequence::pair,
};
use std::{
    fmt::write,
    io::{Read, Result as IoResult, Write},
};

use core::marker::PhantomData;

const NUM_IDENTIFIER_BYTES: usize = 64;

/// An identifier is a string of alphanumeric (and underscore) characters.
/// Identifiers are enforced to be `NUM_IDENTIFIER_BYTES` bytes long.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Identifier<E: Environment>(String, PhantomData<E>);

impl<E: Environment> Identifier<E> {
    /// Create a new identifier from a string.
    pub fn new(identifier: String) -> Self {
        match identifier.len() <= NUM_IDENTIFIER_BYTES {
            true => Self(identifier, PhantomData),
            false => E::halt(format!(
                "Identifier {} is too large. Identifiers must be <= {} bytes long.",
                identifier, NUM_IDENTIFIER_BYTES
            )),
        }
    }

    /// Returns the identifier as a string.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl<E: Environment> Parser for Identifier<E> {
    type Environment = E;

    /// Parses a string into an identifier.
    /// The identifier must be less than or equal to `NUM_IDENTIFIER_BYTES` bytes long.
    /// The identifier must be alphanumeric (and underscore).
    /// The identifier must not start with a number.
    ///
    /// # Example
    /// ```
    /// use snarkvm_circuits_core::Identifier;
    /// use snarkvm_circuits_types::environment::{Circuit, Parser};
    /// let identifier = Identifier::<Circuit>::parse("foo_bar_baz");
    /// assert!(identifier.is_ok());
    /// ```
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Check for alphanumeric characters and underscores.
        map_res(recognize(pair(alpha1, many0(alt((alphanumeric1, tag("_")))))), |name: &str| {
            match name.len() <= NUM_IDENTIFIER_BYTES {
                true => Ok(Self::new(name.to_string())),
                false => Err(error(format!("Failed to parse template identifier of {} bytes", name.len()))),
            }
        })(string)
    }
}

impl<E: Environment> fmt::Display for Identifier<E> {
    /// Prints the identifier as a string.
    /// The identifier must be less than or equal to `NUM_IDENTIFIER_BYTES` bytes long.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_types::environment::Circuit;

    type E = Circuit;

    #[test]
    fn test_identifier_parser() {
        let candidate = Identifier::<E>::parse("foo_bar").unwrap();
        assert_eq!("", candidate.0);
        assert_eq!("foo_bar".to_string(), candidate.1.0);
    }

    #[test]
    fn test_identifier_parser_fail() {
        // Must start with an alphabetic character.
        let identifier = Identifier::<E>::parse("1foo");
        assert!(identifier.is_err());
        // // Must be alphanumeric or underscore.
        // let identifier = Identifier::<E>::parse("foo_bar~baz");
        // assert!(identifier.is_err());
    }
}
