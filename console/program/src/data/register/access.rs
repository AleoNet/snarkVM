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

use crate::{Identifier, U32};

use snarkvm_console_network::prelude::*;

/// A register `Access`.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum Access<N: Network> {
    // TODO (d0cd): Introduce the `Index` variant.
    /// The access is a member.
    Member(Identifier<N>),
}

impl<N: Network> Parser for Access<N> {
    fn parse(string: &str) -> ParserResult<Self>
    where
        Self: Sized,
    {
        alt((map(pair(tag("."), Identifier::parse), |(_, identifier)| Self::Member(identifier)),))(string)
    }
}

impl<N: Network> FromStr for Access<N> {
    type Err = Error;

    /// Parses an identifier into an access.
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
            // Prints the access member, i.e. `.foo`
            Self::Member(identifier) => write!(f, ".{}", identifier),
        }
    }
}

impl<N: Network> Serialize for Access<N> {
    /// Serializes the access into a string or bytes.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => serializer.collect_str(self),
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for Access<N> {
    /// Deserializes the access from a string or bytes.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => FromStr::from_str(&String::deserialize(deserializer)?).map_err(de::Error::custom),
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "access"),
        }
    }
}
