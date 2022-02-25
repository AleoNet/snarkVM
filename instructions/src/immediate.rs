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

use crate::{keyword, ParserResult, Type};
use snarkvm_circuits::{
    Affine,
    BaseField as BaseFieldCircuit,
    Boolean as BooleanCircuit,
    Eject,
    Environment,
    Integer as IntegerCircuit,
    Integer,
    IntegerTrait,
    Mode,
    ScalarField as ScalarFieldCircuit,
    I128,
    I16,
    I32,
    I64,
    I8,
    U128,
    U16,
    U32,
    U64,
    U8,
};

use core::num::ParseIntError;
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{char, one_of},
    combinator::{map, map_res, recognize, value, verify},
    multi::{many0, many1},
    sequence::terminated,
};
use std::iter::FromIterator;

///
/// Immediate
///
// TODO (@pranav) Need a Circuit trait to store immediates.
//   Using Strings for simplicity.
//   Note that this implementation will accept invalid value strings and report an error at a later stage.
pub struct Immediate {
    value: String,
    typ: Type,
}

impl Immediate {
    pub fn new(input: &str) -> ParserResult<Self> {
        // Parse the digits from the input.
        alt((Self::parse_boolean, Self::parse_numerical_immediate))(input)
    }

    fn parse_boolean(input: &str) -> ParserResult<Self> {
        // Parse the boolean from the input.
        let (input, value) = alt((tag("true"), tag("false")))(input)?;
        // Output the remaining input and the initialized boolean.
        Ok((input, Self { value: String::from(value), typ: Type::Boolean }))
    }

    fn parse_numerical_immediate(input: &str) -> ParserResult<Self> {
        // Parse the digits from the input.
        let (input, value) = recognize(many1(terminated(one_of("0123456789"), many0(char('_')))))(input)?;
        // Parse the integer type from the input.
        let (input, typ) = Type::new(input)?;
        Ok((input, Self { value: String::from(value), typ }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use snarkvm_circuits::Circuit;

    use core::str::FromStr;

    #[test]
    fn test_base_new() {
        let (_, imm) = Immediate::new("5base").unwrap();
        assert_eq!(imm.get_type(), Type::BaseField);

        let (_, imm) = Immediate::new("5_base").unwrap();
        assert_eq!(imm.get_type(), Type::BaseField);

        let (_, imm) = Immediate::new("1_5_base").unwrap();
        assert_eq!(imm.get_type(), Type::BaseField);
    }

    #[test]
    fn test_malformed_base() {
        assert!(Immediate::new("5ba_se").is_err());
    }

    #[test]
    fn test_boolean_new() {
        let (_, imm) = Immediate::new("true").unwrap();
        assert_eq!(imm.get_type(), Type::Boolean);

        let (_, imm) = Immediate::new("false").unwrap();
        assert_eq!(imm.get_type(), Type::Boolean);
    }

    #[test]
    fn test_malformed_boolean() {
        assert!(Immediate::new("maybe").is_err());
    }

    #[test]
    fn test_group_new() {
        let (_, imm) = Immediate::new("0group").unwrap();
        assert_eq!(imm.get_type(), Type::Group);

        let (_, imm) = Immediate::new("0_group").unwrap();
        assert_eq!(imm.get_type(), Type::Group);
    }

    #[test]
    fn test_malformed_group() {
        assert!(Immediate::new("0grou_p").is_err());
    }

    #[test]
    fn test_u8() {
        let (_, imm) = Immediate::new("5u8").unwrap();
        assert_eq!(imm.get_type(), Type::U8);

        let (_, imm) = Immediate::new("5_u8").unwrap();
        assert_eq!(imm.get_type(), Type::U8);

        let (_, imm) = Immediate::new("1_5_u8").unwrap();
        assert_eq!(imm.get_type(), Type::U8);
    }

    #[test]
    fn test_malformed_integer() {
        assert!(Immediate::new("5u_8").is_err());
    }

    #[test]
    fn test_scalar_new() {
        let (_, imm) = Immediate::new("5scalar").unwrap();
        assert_eq!(imm.get_type(), Type::ScalarField);

        let (_, imm) = Immediate::new("5_scalar").unwrap();
        assert_eq!(imm.get_type(), Type::ScalarField);

        let (_, imm) = Immediate::new("1_5_scalar").unwrap();
        assert_eq!(imm.get_type(), Type::ScalarField);
    }

    #[test]
    fn test_malformed_scalar() {
        assert!(Immediate::new("5scala_r").is_err());
    }
}
