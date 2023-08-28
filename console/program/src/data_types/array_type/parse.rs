// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;

impl<N: Network> Parser for ArrayType<N> {
    /// Parses a string into a literal type.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the opening bracket.
        let (string, _) = tag("[")(string)?;
        // Parse the whitespaces from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;

        // A helper function to parse the semicolon, length, and closing bracket.
        fn parse_length(string: &str) -> ParserResult<u32> {
            // Parse the whitespaces from the string.
            let (string, _) = Sanitizer::parse_whitespaces(string)?;
            // Parse the semicolon.
            let (string, _) = tag(";")(string)?;
            // Parse the whitespaces from the string.
            let (string, _) = Sanitizer::parse_whitespaces(string)?;
            // Parse the length from the string.
            let (string, length) =
                map_res(recognize(many1(one_of("0123456789"))), |digits: &str| digits.parse::<u32>())(string)?;
            // Parse the whitespaces from the string.
            let (string, _) = Sanitizer::parse_whitespaces(string)?;
            // Parse the closing bracket.
            let (string, _) = tag("]")(string)?;
            Ok((string, length))
        }

        // Parse the element type, followed by the length.
        alt((
            map_res(pair(LiteralType::parse, parse_length), |(element_type, length)| {
                ArrayType::new_literal(element_type, U32::new(length))
            }),
            map_res(pair(Identifier::parse, parse_length), |(element_type, length)| {
                ArrayType::new_struct(element_type, U32::new(length))
            }),
        ))(string)
    }
}

impl<N: Network> FromStr for ArrayType<N> {
    type Err = Error;

    /// Returns an array type from a string literal.
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

impl<N: Network> Debug for ArrayType<N> {
    /// Prints the array type as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for ArrayType<N> {
    /// Prints the array type as a string.
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Literal(literal_type, length) => write!(f, "[{}; {}]", literal_type, **length),
            Self::Struct(identifier, length) => write!(f, "[{}; {}]", identifier, **length),
        }
    }
}
