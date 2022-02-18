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

use crate::{Base, Boolean, Group, Integer, ParserResult, RegisterType, Scalar, TypedRegister};

use nom::{
    bytes::complete::tag,
    character::complete::{char, one_of},
    combinator::verify,
    error::{make_error, ErrorKind, VerboseError, VerboseErrorKind},
    multi::{many0, many1},
    sequence::terminated,
};
use snarkvm_circuits::{Environment, IntegerType};

// TODO (@pranav) If this instruction is needed, then refactor this code.
//  There are a couple options. Operations directly take immediates.
//  Or the specific load operations could be folded into one. Or keep
//  the existing implementation.

pub struct LoadBaseField<E: Environment> {
    rd: TypedRegister,
    imm: Base<E>,
}

impl<E: Environment> LoadBaseField<E> {
    pub fn new(input: &str) -> ParserResult<Self> {
        let (input, _) = tag("loadbf ")(input)?;
        let (input, rd) = TypedRegister::new(input)?;
        let (input, _) = tag(", ")(input)?;
        let (input, imm) = Base::<E>::new(input)?;
        let (input, _) = tag(";")(input)?;
        match rd.as_ref().unwrap().get_type() {
            (RegisterType::BaseField) => {
                let instruction = Self { rd: rd.unwrap(), imm };
                Ok((input, instruction))
            }
            _ => {
                // TODO (@pranav) Invoking a nonsensical error kind while prototyping.
                //   Replace with an appropriate error type.
                Err(nom::Err::Error(VerboseError { errors: vec![(input, VerboseErrorKind::Nom(ErrorKind::Fail))] }))
            }
        }
    }
}

pub struct LoadBoolean<E: Environment> {
    rd: TypedRegister,
    imm: Boolean<E>,
}

impl<E: Environment> LoadBoolean<E> {
    pub fn new(input: &str) -> ParserResult<Self> {
        let (input, _) = tag("loadb ")(input)?;
        let (input, rd) = TypedRegister::new(input)?;
        let (input, _) = tag(", ")(input)?;
        let (input, imm) = Boolean::<E>::new(input)?;
        let (input, _) = tag(";")(input)?;
        match rd.as_ref().unwrap().get_type() {
            (RegisterType::Boolean) => {
                let instruction = Self { rd: rd.unwrap(), imm };
                Ok((input, instruction))
            }
            _ => {
                // TODO (@pranav) Invoking a nonsensical error kind while prototyping.
                //   Replace with an appropriate error type.
                Err(nom::Err::Error(VerboseError { errors: vec![(input, VerboseErrorKind::Nom(ErrorKind::Fail))] }))
            }
        }
    }
}

pub struct LoadGroup<E: Environment> {
    rd: TypedRegister,
    imm: Group<E>,
}

impl<E: Environment> LoadGroup<E> {
    pub fn new(input: &str) -> ParserResult<Self> {
        let (input, _) = tag("loadg ")(input)?;
        let (input, rd) = TypedRegister::new(input)?;
        let (input, _) = tag(", ")(input)?;
        let (input, imm) = Group::<E>::new(input)?;
        let (input, _) = tag(";")(input)?;
        match rd.as_ref().unwrap().get_type() {
            (RegisterType::Group) => {
                let instruction = Self { rd: rd.unwrap(), imm };
                Ok((input, instruction))
            }
            _ => {
                // TODO (@pranav) Invoking a nonsensical error kind while prototyping.
                //   Replace with an appropriate error type.
                Err(nom::Err::Error(VerboseError { errors: vec![(input, VerboseErrorKind::Nom(ErrorKind::Fail))] }))
            }
        }
    }
}

pub struct LoadInteger<E: Environment, I: IntegerType> {
    rd: TypedRegister,
    imm: Integer<E, I>,
}

impl<E: Environment, I: IntegerType> LoadInteger<E, I> {
    pub fn new(input: &str) -> ParserResult<Self> {
        let (input, _) = tag("loadi ")(input)?;
        let (input, rd) = TypedRegister::new(input)?;
        let (input, _) = tag(", ")(input)?;
        let (input, imm) = Integer::<E, I>::new(input)?;
        let (input, _) = tag(";")(input)?;
        match rd.as_ref().unwrap().get_type() {
            // TODO (@pranav) Temporary until we paramaterize the integer register type
            (RegisterType::U8) => {
                let instruction = Self { rd: rd.unwrap(), imm };
                Ok((input, instruction))
            }
            _ => {
                // TODO (@pranav) Invoking a nonsensical error kind while prototyping.
                //   Replace with an appropriate error type.
                Err(nom::Err::Error(VerboseError { errors: vec![(input, VerboseErrorKind::Nom(ErrorKind::Fail))] }))
            }
        }
    }
}

pub struct LoadScalarField<E: Environment> {
    rd: TypedRegister,
    imm: Scalar<E>,
}

impl<E: Environment> LoadScalarField<E> {
    pub fn new(input: &str) -> ParserResult<Self> {
        let (input, _) = tag("loadsf ")(input)?;
        let (input, rd) = TypedRegister::new(input)?;
        let (input, _) = tag(", ")(input)?;
        let (input, imm) = Scalar::<E>::new(input)?;
        let (input, _) = tag(";")(input)?;
        match rd.as_ref().unwrap().get_type() {
            (RegisterType::ScalarField) => {
                let instruction = Self { rd: rd.unwrap(), imm };
                Ok((input, instruction))
            }
            _ => {
                // TODO (@pranav) Invoking a nonsensical error kind while prototyping.
                //   Replace with an appropriate error type.
                Err(nom::Err::Error(VerboseError { errors: vec![(input, VerboseErrorKind::Nom(ErrorKind::Fail))] }))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::str::FromStr;
    use snarkvm_circuits::Circuit;

    #[test]
    fn test_load_new() {
        type E = Circuit;
        // TODO (@pranav)
        //  This is just a sanity check. Need to construct a comprehensive test framework.
        let (_, load_instruction) = LoadBaseField::<E>::new("loadbf bf.r3, 5base;").unwrap();
        assert_eq!(3, load_instruction.rd.get_id());
        assert_eq!(RegisterType::BaseField, load_instruction.rd.get_type());

        let (_, load_instruction) = LoadBoolean::<E>::new("loadb b.r3, true;").unwrap();
        assert_eq!(3, load_instruction.rd.get_id());
        assert_eq!(RegisterType::Boolean, load_instruction.rd.get_type());

        let (_, load_instruction) = LoadGroup::<E>::new("loadg g.r3, 0group;").unwrap();
        assert_eq!(3, load_instruction.rd.get_id());
        assert_eq!(RegisterType::Group, load_instruction.rd.get_type());

        let (_, load_instruction) = LoadInteger::<E, u8>::new("loadi u8.r3, 255u8;").unwrap();
        assert_eq!(3, load_instruction.rd.get_id());
        assert_eq!(RegisterType::U8, load_instruction.rd.get_type());

        let (_, load_instruction) = LoadScalarField::<E>::new("loadsf sf.r3, 5scalar;").unwrap();
        assert_eq!(3, load_instruction.rd.get_id());
        assert_eq!(RegisterType::ScalarField, load_instruction.rd.get_type());
    }

    #[test]
    fn test_malformed_add() {
        todo!()
    }
}
