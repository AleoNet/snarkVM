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
/// Typed registers have the syntactic form <RegisterType>.r<N>
///
// TODO (@pranav) Instead of a single typed register, consider having explicit
//  register structs for each of the types. This would result in stronger type
//  restrictions for instructions.

pub enum Immediate<E: Environment> {
    BaseField(BaseFieldCircuit<E>),
    Boolean(BooleanCircuit<E>),
    Group(Affine<E>),
    U8(IntegerCircuit<E, u8>),
    U16(IntegerCircuit<E, u16>),
    U32(IntegerCircuit<E, u32>),
    U64(IntegerCircuit<E, u64>),
    U128(IntegerCircuit<E, u128>),
    I8(IntegerCircuit<E, i8>),
    I16(IntegerCircuit<E, i16>),
    I32(IntegerCircuit<E, i32>),
    I64(IntegerCircuit<E, i64>),
    I128(IntegerCircuit<E, i128>),
    ScalarField(ScalarFieldCircuit<E>),
}

impl<E: Environment> Immediate<E> {
    pub fn new(input: &str) -> ParserResult<Self> {
        // Parse the digits from the input.
        alt((Self::parse_boolean, Self::parse_numerical_immediate))(input)
    }

    pub fn get_value(&self) -> Type {
        match self {
            Immediate::BaseField(circuit)
            | Immediate::Boolean(circuit)
            | Immediate::Group(circuit)
            | Immediate::U8(circuit)
            | Immediate::U16(circuit)
            | Immediate::U32(circuit)
            | Immediate::U64(circuit)
            | Immediate::U128(circuit)
            | Immediate::I8(circuit)
            | Immediate::I16(circuit)
            | Immediate::I32(circuit)
            | Immediate::I64(circuit)
            | Immediate::I128(circuit)
            | Immediate::ScalarField(circuit) => circuit.eject_value(),
        }
    }

    pub fn get_type(&self) -> Type {
        match self {
            Immediate::BaseField(_) => Type::BaseField,
            Immediate::Boolean(_) => Type::Boolean,
            Immediate::Group(_) => Type::Group,
            Immediate::U8(_) => Type::U8,
            Immediate::U16(_) => Type::U16,
            Immediate::U32(_) => Type::U32,
            Immediate::U64(_) => Type::U64,
            Immediate::U128(_) => Type::U128,
            Immediate::I8(_) => Type::I8,
            Immediate::I16(_) => Type::I16,
            Immediate::I32(_) => Type::I32,
            Immediate::I64(_) => Type::I64,
            Immediate::I128(_) => Type::I128,
            Immediate::ScalarField(_) => Type::ScalarField,
        }
    }

    fn parse_boolean(input: &str) -> ParserResult<Self> {
        // Parse the boolean from the input.
        let (input, boolean) = alt((value(true, keyword("true")), value(false, keyword("false"))))(input)?;
        // Output the remaining input and the initialized boolean.
        Ok((input, Self::Boolean(BooleanCircuit::new(Mode::Constant, boolean))))
    }

    // TODO (@pranav) Replace unwraps with better error messages.
    fn parse_numerical_immediate(input: &str) -> ParserResult<Self> {
        // Parse the digits from the input.
        let (input, value) = recognize(many1(terminated(one_of("0123456789"), many0(char('_')))))(input)?;
        // Parse the integer type from the input.
        let mut parse_type = alt((
            map(tag("base"), |_| {
                Self::BaseField(BaseFieldCircuit::new(Mode::Constant, value.parse::<E::BaseField>().unwrap()))
            }),
            map(tag("group"), |_| {
                Self::Group(Affine::new(Mode::Constant, value.parse::<E::BaseField>().unwrap(), None))
            }),
            map(tag("i8"), |_| Self::I8(I8::new(Mode::Constant, value.parse::<i8>().unwrap()))),
            map(tag("i16"), |_| Self::I16(I16::new(Mode::Constant, value.parse::<i16>().unwrap()))),
            map(tag("i32"), |_| Self::I32(I32::new(Mode::Constant, value.parse::<i32>().unwrap()))),
            map(tag("i64"), |_| Self::I64(I64::new(Mode::Constant, value.parse::<i64>().unwrap()))),
            map(tag("i128"), |_| Self::I128(I128::new(Mode::Constant, value.parse::<i128>().unwrap()))),
            map(tag("u8"), |_| Self::U8(U8::new(Mode::Constant, value.parse::<u8>().unwrap()))),
            map(tag("u16"), |_| Self::U16(U16::new(Mode::Constant, value.parse::<u16>().unwrap()))),
            map(tag("u32"), |_| Self::U32(U32::new(Mode::Constant, value.parse::<u32>().unwrap()))),
            map(tag("u64"), |_| Self::U64(U64::new(Mode::Constant, value.parse::<u64>().unwrap()))),
            map(tag("u128"), |_| Self::U128(U128::new(Mode::Constant, value.parse::<u128>().unwrap()))),
            map(tag("scalar"), |_| {
                Self::ScalarField(ScalarFieldCircuit::new(Mode::Constant, value.parse::<E::ScalarField>().unwrap()))
            }),
        ));
        parse_type(input)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use snarkvm_circuits::Circuit;

    use core::str::FromStr;
    use std::matches;

    #[test]
    fn test_base_new() {
        type E = Circuit;
        let (_, imm) = Immediate::<E>::new("5base").unwrap();
        assert!(matches!(imm, Immediate::BaseField(_)));
        assert_eq!(
            <E as Environment>::BaseField::from_str("5").unwrap(),
            imm.get_value()
        );

        let (_, imm) = Immediate::<E>::new("5_base").unwrap();
        assert!(matches!(imm, Immediate::BaseField(_)));
        assert_eq!(
            <E as Environment>::BaseField::from_str("5").unwrap(),
            imm.get_value()
        );

        let (_, imm) = Immediate::<E>::new("1_5_base").unwrap();
        assert!(matches!(imm, Immediate::BaseField(_)));
        assert_eq!(
            <E as Environment>::BaseField::from_str("15").unwrap(),
            imm.get_value()
        );
    }

    #[test]
    fn test_malformed_base() {
        type E = Circuit;
        assert!(Immediate::<E>::new("5ba_se").is_err());
    }

    #[test]
    fn test_boolean_new() {
        type E = Circuit;
        let (_, imm) = Immediate::<E>::new("true").unwrap();
        assert!(matches!(imm, Immediate::Boolean(_)));
        assert_eq!(true, imm.get_value());

        let (_, imm) = Immediate::<E>::new("false").unwrap();
        assert!(matches!(imm, Immediate::Boolean(_)));
        assert_eq!(false, imm.get_value());
    }

    #[test]
    fn test_malformed_boolean() {
        type E = Circuit;
        assert!(Immediate::<E>::new("maybe").is_err());
        assert!(Immediate::<E>::new("truee").is_err());
        assert!(Immediate::<E>::new("truefalse").is_err());
        assert!(Immediate::<E>::new("falsetrue").is_err());
    }

    #[test]
    fn test_group_new() {
        type E = Circuit;
        let (_, imm) = Immediate::<E>::new("0group").unwrap();
        assert!(matches!(imm, Immediate::Group(_)));
        assert_eq!(
            E::affine_from_x_coordinate(<E as Environment>::BaseField::from_str("0").unwrap()),
            imm.get_value()
        );

        let (_, imm) = Immediate::<E>::new("0_group").unwrap();
        assert!(matches!(imm, Immediate::Group(_)));
        assert_eq!(
            E::affine_from_x_coordinate(<E as Environment>::BaseField::from_str("0").unwrap()),
            imm.get_value()
        );
    }

    #[test]
    fn test_malformed_group() {
        type E = Circuit;
        assert!(Immediate::<E>::new("0grou_p").is_err());
    }

    #[test]
    fn test_u8() {
        type E = Circuit;
        let (_, imm) = Immediate::<E>::new("5u8").unwrap();
        assert!(matches!(imm, Immediate::U8(_)));
        assert_eq!(5u8, imm.get_value());

        let (_, imm) = Immediate::<E>::new("5_u8").unwrap();
        assert!(matches!(imm, Immediate::U8(_)));
        assert_eq!(5u8, imm.get_value());

        let (_, imm) = Immediate::<E>::new("1_5_u8").unwrap();
        assert!(matches!(imm, Immediate::U8(_)));
        assert_eq!(15u8, imm.get_value());
    }

    #[test]
    fn test_malformed_integer() {
        type E = Circuit;
        assert!(Immediate::<E>::new("5u_8").is_err());
    }

    #[test]
    fn test_scalar_new() {
        type E = Circuit;
        let (_, imm) = Immediate::<E>::new("5scalar").unwrap();
        assert!(matches!(imm, Immediate::ScalarField(_)));
        assert_eq!(
            <E as Environment>::ScalarField::from_str("5").unwrap(),
            imm.get_value()
        );

        let (_, imm) = Immediate::<E>::new("5_scalar").unwrap();
        assert!(matches!(imm, Immediate::ScalarField(_)));
        assert_eq!(
            <E as Environment>::ScalarField::from_str("5").unwrap(),
            imm.get_value()
        );

        let (_, imm) = Immediate::<E>::new("1_5_scalar").unwrap();
        assert!(matches!(imm, Immediate::ScalarField(_)));
        assert_eq!(
            <E as Environment>::ScalarField::from_str("5").unwrap(),
            imm.get_value()
        );
    }

    #[test]
    fn test_malformed_scalar() {
        type E = Circuit;
        assert!(Immediate::<E>::new("5scala_r").is_err());
    }
}
