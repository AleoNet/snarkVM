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

impl<N: Network> Parser for Literal<N> {
    /// Parses a string into a literal.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        alt((
            map(Address::<N>::parse, |literal| Self::Address(literal)),
            map(Boolean::<N>::parse, |literal| Self::Boolean(literal)),
            map(Field::<N>::parse, |literal| Self::Field(literal)),
            map(Group::<N>::parse, |literal| Self::Group(literal)),
            map(I8::<N>::parse, |literal| Self::I8(literal)),
            map(I16::<N>::parse, |literal| Self::I16(literal)),
            map(I32::<N>::parse, |literal| Self::I32(literal)),
            map(I64::<N>::parse, |literal| Self::I64(literal)),
            map(I128::<N>::parse, |literal| Self::I128(literal)),
            map(U8::<N>::parse, |literal| Self::U8(literal)),
            map(U16::<N>::parse, |literal| Self::U16(literal)),
            map(U32::<N>::parse, |literal| Self::U32(literal)),
            map(U64::<N>::parse, |literal| Self::U64(literal)),
            map(U128::<N>::parse, |literal| Self::U128(literal)),
            map(Scalar::<N>::parse, |literal| Self::Scalar(literal)),
            map(StringType::<N>::parse, |literal| Self::String(literal)),
        ))(string)
    }
}

impl<N: Network> FromStr for Literal<N> {
    type Err = Error;

    /// Parses a string into a literal.
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

impl<N: Network> Debug for Literal<N> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Literal<N> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Self::Address(literal) => Display::fmt(literal, f),
            Self::Boolean(literal) => Display::fmt(literal, f),
            Self::Field(literal) => Display::fmt(literal, f),
            Self::Group(literal) => Display::fmt(literal, f),
            Self::I8(literal) => Display::fmt(literal, f),
            Self::I16(literal) => Display::fmt(literal, f),
            Self::I32(literal) => Display::fmt(literal, f),
            Self::I64(literal) => Display::fmt(literal, f),
            Self::I128(literal) => Display::fmt(literal, f),
            Self::U8(literal) => Display::fmt(literal, f),
            Self::U16(literal) => Display::fmt(literal, f),
            Self::U32(literal) => Display::fmt(literal, f),
            Self::U64(literal) => Display::fmt(literal, f),
            Self::U128(literal) => Display::fmt(literal, f),
            Self::Scalar(literal) => Display::fmt(literal, f),
            Self::String(literal) => Display::fmt(literal, f),
        }
    }
}
