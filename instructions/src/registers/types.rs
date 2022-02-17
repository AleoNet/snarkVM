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
use nom::{branch::alt, bytes::complete::tag};

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum RegisterType {
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

impl RegisterType {
    pub fn new(input: &str) -> ParserResult<Result<Self, ParseIntError>> {
        let mut parse_type = alt((
            Self::parse_base_field_type,
            Self::parse_boolean_type,
            Self::parse_group_type,
            Self::parse_i8_type,
            Self::parse_i16_type,
            Self::parse_i32_type,
            Self::parse_i64_type,
            Self::parse_i128_type,
            Self::parse_scalar_field_type,
            Self::parse_u8_type,
            Self::parse_u16_type,
            Self::parse_u32_type,
            Self::parse_u64_type,
            Self::parse_u128_type,
        ));
        parse_type(input)
    }

    fn parse_base_field_type(input: &str) -> ParserResult<Result<Self, ParseIntError>> {
        let (input, _) = tag("bf")(input)?;
        Ok((input, Ok(Self::BaseField)))
    }

    fn parse_boolean_type(input: &str) -> ParserResult<Result<Self, ParseIntError>> {
        let (input, _) = tag("b")(input)?;
        Ok((input, Ok(Self::Boolean)))
    }

    fn parse_group_type(input: &str) -> ParserResult<Result<Self, ParseIntError>> {
        let (input, _) = tag("g")(input)?;
        Ok((input, Ok(Self::Group)))
    }

    fn parse_i8_type(input: &str) -> ParserResult<Result<Self, ParseIntError>> {
        let (input, _) = tag("i8")(input)?;
        Ok((input, Ok(Self::I8)))
    }

    fn parse_i16_type(input: &str) -> ParserResult<Result<Self, ParseIntError>> {
        let (input, _) = tag("i16")(input)?;
        Ok((input, Ok(Self::I16)))
    }

    fn parse_i32_type(input: &str) -> ParserResult<Result<Self, ParseIntError>> {
        let (input, _) = tag("i32")(input)?;
        Ok((input, Ok(Self::I32)))
    }

    fn parse_i64_type(input: &str) -> ParserResult<Result<Self, ParseIntError>> {
        let (input, _) = tag("i64")(input)?;
        Ok((input, Ok(Self::I64)))
    }

    fn parse_i128_type(input: &str) -> ParserResult<Result<Self, ParseIntError>> {
        let (input, _) = tag("i128")(input)?;
        Ok((input, Ok(Self::I128)))
    }

    fn parse_scalar_field_type(input: &str) -> ParserResult<Result<Self, ParseIntError>> {
        let (input, _) = tag("sf")(input)?;
        Ok((input, Ok(Self::ScalarField)))
    }

    fn parse_u8_type(input: &str) -> ParserResult<Result<Self, ParseIntError>> {
        let (input, _) = tag("u8")(input)?;
        Ok((input, Ok(Self::U8)))
    }

    fn parse_u16_type(input: &str) -> ParserResult<Result<Self, ParseIntError>> {
        let (input, _) = tag("u16")(input)?;
        Ok((input, Ok(Self::U16)))
    }

    fn parse_u32_type(input: &str) -> ParserResult<Result<Self, ParseIntError>> {
        let (input, _) = tag("u32")(input)?;
        Ok((input, Ok(Self::U32)))
    }

    fn parse_u64_type(input: &str) -> ParserResult<Result<Self, ParseIntError>> {
        let (input, _) = tag("u64")(input)?;
        Ok((input, Ok(Self::U64)))
    }

    fn parse_u128_type(input: &str) -> ParserResult<Result<Self, ParseIntError>> {
        let (input, _) = tag("u128")(input)?;
        Ok((input, Ok(Self::U128)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // TODO (@pranav)
    //  This is just a sanity check. Need to construct a comprehensive test framework.
    #[test]
    fn test_type_new() {
        assert_eq!(RegisterType::BaseField, RegisterType::new("bf").unwrap().1.unwrap());
        assert_eq!(RegisterType::Boolean, RegisterType::new("b").unwrap().1.unwrap());
        assert_eq!(RegisterType::Group, RegisterType::new("g").unwrap().1.unwrap());
        assert_eq!(RegisterType::I8, RegisterType::new("i8").unwrap().1.unwrap());
        assert_eq!(RegisterType::I16, RegisterType::new("i16").unwrap().1.unwrap());
        assert_eq!(RegisterType::I32, RegisterType::new("i32").unwrap().1.unwrap());
        assert_eq!(RegisterType::I64, RegisterType::new("i64").unwrap().1.unwrap());
        assert_eq!(RegisterType::I128, RegisterType::new("i128").unwrap().1.unwrap());
        assert_eq!(RegisterType::ScalarField, RegisterType::new("sf").unwrap().1.unwrap());
        assert_eq!(RegisterType::U8, RegisterType::new("u8").unwrap().1.unwrap());
        assert_eq!(RegisterType::U16, RegisterType::new("u16").unwrap().1.unwrap());
        assert_eq!(RegisterType::U32, RegisterType::new("u32").unwrap().1.unwrap());
        assert_eq!(RegisterType::U64, RegisterType::new("u64").unwrap().1.unwrap());
        assert_eq!(RegisterType::U128, RegisterType::new("u128").unwrap().1.unwrap());
    }
}
