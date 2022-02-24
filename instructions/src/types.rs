// Copyright (C) 2019-2021 Aleo Systems Inc.
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

use crate::ParserResult;

use core::num::ParseIntError;
use nom::{branch::alt, bytes::complete::tag, combinator::map, Parser};

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Type {
    BaseField,
    Boolean,
    Group,
    I8,
    I16,
    I32,
    I64,
    I128,
    ScalarField,
    U8,
    U16,
    U32,
    U64,
    U128,
}

impl Type {
    pub fn new(input: &str) -> ParserResult<Self> {
        alt((
            map(tag("base"), |_| Self::BaseField),
            map(tag("bool"), |_| Self::Boolean),
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
            map(tag("scalar"), |_| Self::ScalarField),
        ))(input)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // TODO (@pranav)
    //  This is just a sanity check. Need to construct a comprehensive test framework.
    #[test]
    fn test_type_new() {
        assert_eq!(Type::BaseField, Type::new("bf").unwrap().1.unwrap());
        assert_eq!(Type::Boolean, Type::new("b").unwrap().1.unwrap());
        assert_eq!(Type::Group, Type::new("g").unwrap().1.unwrap());
        assert_eq!(Type::I8, Type::new("i8").unwrap().1.unwrap());
        assert_eq!(Type::I16, Type::new("i16").unwrap().1.unwrap());
        assert_eq!(Type::I32, Type::new("i32").unwrap().1.unwrap());
        assert_eq!(Type::I64, Type::new("i64").unwrap().1.unwrap());
        assert_eq!(Type::I128, Type::new("i128").unwrap().1.unwrap());
        assert_eq!(Type::ScalarField, Type::new("sf").unwrap().1.unwrap());
        assert_eq!(Type::U8, Type::new("u8").unwrap().1.unwrap());
        assert_eq!(Type::U16, Type::new("u16").unwrap().1.unwrap());
        assert_eq!(Type::U32, Type::new("u32").unwrap().1.unwrap());
        assert_eq!(Type::U64, Type::new("u64").unwrap().1.unwrap());
        assert_eq!(Type::U128, Type::new("u128").unwrap().1.unwrap());
    }
}
