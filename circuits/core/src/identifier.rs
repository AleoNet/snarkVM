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
use snarkvm_utilities::error;

use core::{fmt, marker::PhantomData};
use nom::character::complete::{alpha1, alphanumeric1};

const NUM_IDENTIFIER_BYTES: usize = 64;
// TODO (howardwu): Add the instruction opcodes, and the literal type names.
const KEYWORDS: [&str; 10] =
    ["constant", "field", "function", "input", "output", "parameter", "public", "private", "record", "template"];

/// An identifier is a string of alphanumeric (and underscore) characters.
///
/// # Requirements
/// The identifier must be less than or equal to `NUM_IDENTIFIER_BYTES` bytes long.
/// The identifier must be alphanumeric (or underscore).
/// The identifier must not start with a number.
/// The identifier must not be a keyword.
///
/// # Example
/// ```
/// use snarkvm_circuits_core::Identifier;
/// use snarkvm_circuits_types::environment::Circuit;
/// let identifier = Identifier::<Circuit>::new("foo");
/// assert_eq!(identifier.to_string(), "foo");
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Identifier<E: Environment>(String, PhantomData<E>);

impl<E: Environment> Identifier<E> {
    /// Create a new identifier from a string.
    pub fn new(identifier: &str) -> Self {
        Self::from_str(identifier)
    }

    /// Returns the identifier as a string.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl<E: Environment> Parser for Identifier<E> {
    type Environment = E;

    /// Parses a string into an identifier.
    ///
    /// # Requirements
    /// The identifier must be less than or equal to `NUM_IDENTIFIER_BYTES` bytes long.
    /// The identifier must be alphanumeric (or underscore).
    /// The identifier must not start with a number.
    /// The identifier must not be a keyword.
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
        map_res(recognize(pair(alpha1, many0(alt((alphanumeric1, tag("_")))))), |identifier: &str| {
            // Ensure identifier is less than or equal to `NUM_IDENTIFIER_BYTES` bytes long.
            if identifier.len() > NUM_IDENTIFIER_BYTES {
                return Err(error(format!(
                    "Identifier is too large. Identifiers must be <= {NUM_IDENTIFIER_BYTES} bytes long",
                )));
            }

            // TODO (howardwu): Use `if E::keywords().contains(name)` instead of `KEYWORDS.contains(name)`.
            // Ensure identifier is not a keyword.
            if KEYWORDS.contains(&identifier) {
                // if E::keywords().contains(name) {
                return Err(error(format!("Identifier `{}` is a keyword", identifier)));
            }

            Ok(Self(identifier.to_string(), PhantomData))
        })(string)
    }
}

impl<E: Environment> fmt::Display for Identifier<E> {
    /// Prints the identifier as a string.
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
    fn test_identifier_parse() {
        let candidate = Identifier::<E>::parse("foo_bar").unwrap();
        assert_eq!("", candidate.0);
        assert_eq!("foo_bar".to_string(), candidate.1.0);
    }

    #[test]
    fn test_identifier_parse_fails() {
        // Must be less than or equal to `NUM_IDENTIFIER_BYTES` bytes long.
        let identifier = Identifier::<E>::parse("foo_bar_baz_qux_quux_quuz_corge_grault_garply_waldo_fred_plugh_xyzzy");
        assert!(identifier.is_err());
        // Must be alphanumeric or underscore.
        assert_eq!(Ok(("~baz", Identifier::<E>::new("foo_bar"))), Identifier::<E>::parse("foo_bar~baz"));
        assert_eq!(Ok(("-baz", Identifier::<E>::new("foo_bar"))), Identifier::<E>::parse("foo_bar-baz"));
        // Must not start with a number.
        assert!(Identifier::<E>::parse("2").is_err());
        assert!(Identifier::<E>::parse("1foo").is_err());
        //Must not be a keyword.
        assert!(Identifier::<E>::parse("input").is_err());
        assert!(Identifier::<E>::parse("record").is_err());
    }
}
