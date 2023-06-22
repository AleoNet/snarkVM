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

impl<N: Network> Parser for Access<N> {
    fn parse(string: &str) -> ParserResult<Self>
    where
        Self: Sized,
    {
        // Parse to determine the access.
        alt((
            map_res(
                pair(tag("["), pair(recognize(many1(one_of("0123456789"))), tag("]"))),
                |(_, (digits, _)): (&str, (&str, &str))| {
                    digits.parse::<u32>().map(|index| Self::Index(U32::new(index)))
                },
            ),
            map(pair(tag("."), Identifier::parse), |(_, identifier)| Self::Member(identifier)),
        ))(string)
    }
}

impl<N: Network> FromStr for Access<N> {
    type Err = Error;

    /// Parses a u32 or identifier into an access.
    #[inline]
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

impl<N: Network> Debug for Access<N> {
    /// Prints the access as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Access<N> {
    /// Prints the access as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            // Prints the access index, i.e. `[12]`
            Self::Index(index) => write!(f, "[{}]", index),
            // Prints the access member, i.e. `.foo`
            Self::Member(identifier) => write!(f, ".{}", identifier),
        }
    }
}
