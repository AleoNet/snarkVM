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

use crate::{helpers::Register, Program};
use snarkvm_circuits::prelude::*;
use snarkvm_utilities::{error, FromBytes, ToBytes};

use core::{fmt, marker::PhantomData};
use nom::character::complete::{alpha1, alphanumeric1};
use std::io::{Read, Result as IoResult, Write};

#[rustfmt::skip]
const KEYWORDS: &[&str] = &[
    // Mode
    "constant",
    "public",
    "private",
    // Literals
    "address",
    "boolean",
    "field",
    "group",
    "i8",
    "i16",
    "i32",
    "i64",
    "i128",
    "u8",
    "u16",
    "u32",
    "u64",
    "u128",
    "scalar",
    "string",
    // Boolean
    "true",
    "false",
    // TODO (howardwu): Add the instruction opcodes.
    // Statements
    "input",
    "output",
    // Reserved (catch all)
    "function",
    "type",
    "as",
    "record",
];

/// An identifier is a string of alphanumeric (and underscore) characters.
///
/// # Requirements
/// The identifier must be less than or equal to `NUM_IDENTIFIER_BYTES` bytes long.
/// The identifier must be alphanumeric (or underscore).
/// The identifier must not start with a number.
/// The identifier must not be a keyword.
/// The identifier must not be a register format.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Identifier<P: Program>(String, PhantomData<P>);

impl<P: Program> Identifier<P> {
    /// Returns the identifier as a string.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl<P: Program> Parser for Identifier<P> {
    type Environment = P::Environment;

    /// Parses a string into an identifier.
    ///
    /// # Requirements
    /// The identifier must be less than or equal to `NUM_IDENTIFIER_BYTES` bytes long.
    /// The identifier must be alphanumeric (or underscore).
    /// The identifier must not start with a number.
    /// The identifier must not be a keyword.
    /// The identifier must not be a register format.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Check for alphanumeric characters and underscores.
        map_res(recognize(pair(alpha1, many0(alt((alphanumeric1, tag("_")))))), |identifier: &str| {
            // Ensure identifier is less than or equal to `NUM_IDENTIFIER_BYTES` bytes long.
            if identifier.len() > P::NUM_IDENTIFIER_BYTES {
                return Err(error(format!(
                    "Identifier is too large. Identifiers must be <= {} bytes long",
                    P::NUM_IDENTIFIER_BYTES
                )));
            }

            // TODO (howardwu): Use `if E::keywords().contains(name)` instead of `KEYWORDS.contains(name)`.
            // Ensure identifier is not a keyword.
            if KEYWORDS.contains(&identifier) {
                // if E::keywords().contains(name) {
                return Err(error(format!("Identifier `{identifier}` is a keyword")));
            }

            // Ensure the identifier is not a register format.
            if Register::<P>::parse(identifier).is_ok() {
                return Err(error(format!("Identifier `{identifier}` cannot be of a register format")));
            }

            Ok(Self(identifier.to_string(), PhantomData))
        })(string)
    }
}

impl<P: Program> fmt::Display for Identifier<P> {
    /// Prints the identifier as a string.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl<P: Program> FromBytes for Identifier<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let size = u16::read_le(&mut reader)?;
        let mut buffer = vec![0u8; size as usize];
        reader.read_exact(&mut buffer)?;
        Ok(Self::from_str(
            &String::from_utf8(buffer).map_err(|e| error(format!("Failed to deserialize identifier: {e}")))?,
        ))
    }
}

impl<P: Program> ToBytes for Identifier<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        (self.0.as_bytes().len() as u16).write_le(&mut writer)?;
        self.0.as_bytes().write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Process;

    type P = Process;

    #[test]
    fn test_identifier_parse() {
        let candidate = Identifier::<P>::parse("foo_bar").unwrap();
        assert_eq!("", candidate.0);
        assert_eq!("foo_bar".to_string(), candidate.1.0);
    }

    #[test]
    fn test_identifier_parse_fails() {
        // Must be less than or equal to `NUM_IDENTIFIER_BYTES` bytes long.
        let identifier = Identifier::<P>::parse("foo_bar_baz_qux_quux_quuz_corge_grault_garply_waldo_fred_plugh_xyzzy");
        assert!(identifier.is_err());
        // Must be alphanumeric or underscore.
        assert_eq!(Ok(("~baz", Identifier::<P>::from_str("foo_bar"))), Identifier::<P>::parse("foo_bar~baz"));
        assert_eq!(Ok(("-baz", Identifier::<P>::from_str("foo_bar"))), Identifier::<P>::parse("foo_bar-baz"));
        // Must not start with a number.
        assert!(Identifier::<P>::parse("2").is_err());
        assert!(Identifier::<P>::parse("1foo").is_err());
        // Must not be a keyword.
        assert!(Identifier::<P>::parse("input").is_err());
        assert!(Identifier::<P>::parse("record").is_err());
        // Must not be a register format.
        assert!(Identifier::<P>::parse("r0").is_err());
        assert!(Identifier::<P>::parse("r123").is_err());
        assert!(Identifier::<P>::parse("r0.owner").is_err());
    }

    #[test]
    fn test_identifier_display() {
        let identifier = Identifier::<P>::from_str("foo_bar");
        assert_eq!("foo_bar", format!("{}", identifier));
    }
}
