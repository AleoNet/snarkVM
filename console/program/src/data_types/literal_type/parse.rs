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

use super::*;

impl Parser for LiteralType {
    /// Parses a string into a literal type.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the type from the string.
        alt((
            map(tag("address"), |_| Self::Address),
            map(tag("boolean"), |_| Self::Boolean),
            map(tag("field"), |_| Self::Field),
            map(tag("group"), |_| Self::Group),
            map(tag("i8"), |_| Self::I8),
            map(tag("i16"), |_| Self::I16),
            map(tag("i32"), |_| Self::I32),
            map(tag("i64"), |_| Self::I64),
            map(tag("i128"), |_| Self::I128),
            map(tag("u8"), |_| Self::U8),
            map(tag("u16"), |_| Self::U16),
            map(tag("u32"), |_| Self::U32),
            map(tag("u64"), |_| Self::U64),
            map(tag("u128"), |_| Self::U128),
            map(tag("scalar"), |_| Self::Scalar),
            map(tag("string"), |_| Self::String),
        ))(string)
    }
}

impl FromStr for LiteralType {
    type Err = Error;

    /// Returns a literal type from a string literal.
    fn from_str(string: &str) -> Result<Self> {
        match Self::parse(string) {
            Ok((remainder, object)) => {
                // Ensure the remainder is empty.
                ensure!(remainder.is_empty(), "Failed to parse string. Found invalid character in: \"{remainder}\"");
                // Return the object.
                Ok(object)
            }
            Err(error) => bail!("Failed to parse string. {error}"),
        }
    }
}

impl Debug for LiteralType {
    /// Prints the literal type as a string.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.type_name())
    }
}

impl Display for LiteralType {
    /// Prints the literal type as a string.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.type_name())
    }
}
