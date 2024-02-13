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

impl<N: Network> Parser for LiteralType<N> {
    /// Parses a string into a literal type.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the type from the string.
        alt((
            map(tag("address"), |_| Self::Address),
            map(tag("boolean"), |_| Self::Boolean),
            map(pair((tag("data["), pair(U32::parse, tag("]"))), |(_, (length, _))| Self::Data(length))),
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
            map(tag("signature"), |_| Self::Signature),
            map(tag("string"), |_| Self::String),
        ))(string)
    }
}

impl<N: Network> FromStr for LiteralType<N> {
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

impl<N: Network> Debug for LiteralType<N> {
    /// Prints the literal type as a string.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            LiteralType::Address => write!(f, "address"),
            LiteralType::Boolean => write!(f, "boolean"),
            LiteralType::Data(length) => write!(f, "data({length})"),
            LiteralType::Field => write!(f, "field"),
            LiteralType::Group => write!(f, "group"),
            LiteralType::I8 => write!(f, "i8"),
            LiteralType::I16 => write!(f, "i16"),
            LiteralType::I32 => write!(f, "i32"),
            LiteralType::I64 => write!(f, "i64"),
            LiteralType::I128 => write!(f, "i128"),
            LiteralType::U8 => write!(f, "u8"),
            LiteralType::U16 => write!(f, "u16"),
            LiteralType::U32 => write!(f, "u32"),
            LiteralType::U64 => write!(f, "u64"),
            LiteralType::U128 => write!(f, "u128"),
            LiteralType::Scalar => write!(f, "scalar"),
            LiteralType::Signature => write!(f, "signature"),
            LiteralType::String => write!(f, "string"),
        }
    }
}

impl<N: Network> Display for LiteralType<N> {
    /// Prints the literal type as a string.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", &self)
    }
}
