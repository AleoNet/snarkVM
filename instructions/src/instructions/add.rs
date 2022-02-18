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

use crate::{ParserResult, RegisterType, TypedRegister};

use nom::{
    bytes::complete::tag,
    character::complete::{char, one_of},
    combinator::verify,
    error::{make_error, ErrorKind, VerboseError, VerboseErrorKind},
    multi::{many0, many1},
    sequence::terminated,
};

pub struct Add {
    rd: TypedRegister,
    rs1: TypedRegister,
    rs2: TypedRegister,
}

impl Add {
    pub fn new(input: &str) -> ParserResult<Self> {
        let (input, _) = tag("add ")(input)?;
        let (input, rd) = TypedRegister::new(input)?;
        let (input, _) = tag(", ")(input)?;
        let (input, rs1) = TypedRegister::new(input)?;
        let (input, _) = tag(", ")(input)?;
        let (input, rs2) = TypedRegister::new(input)?;
        let (input, _) = tag(";")(input)?;
        match (rd.as_ref().unwrap().get_type(), rs1.as_ref().unwrap().get_type(), rs2.as_ref().unwrap().get_type()) {
            (RegisterType::BaseField, RegisterType::BaseField, RegisterType::BaseField)
            | (RegisterType::Group, RegisterType::Group, RegisterType::Group)
            | (RegisterType::ScalarField, RegisterType::ScalarField, RegisterType::ScalarField) => {
                let instruction = Self { rd: rd.unwrap(), rs1: rs1.unwrap(), rs2: rs2.unwrap() };
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

    #[test]
    fn test_add_new() {
        // TODO (@pranav)
        //  This is just a sanity check. Need to construct a comprehensive test framework.
        let (_, add_instruction) = Add::new("add bf.r3, bf.r2, bf.r1;").unwrap();
        assert_eq!(3, add_instruction.rd.get_id());
        assert_eq!(2, add_instruction.rs1.get_id());
        assert_eq!(1, add_instruction.rs2.get_id());
        assert_eq!(RegisterType::BaseField, add_instruction.rd.get_type());
        assert_eq!(RegisterType::BaseField, add_instruction.rs1.get_type());
        assert_eq!(RegisterType::BaseField, add_instruction.rs2.get_type());

        let (_, add_instruction) = Add::new("add g.r3, g.r2, g.r1;").unwrap();
        assert_eq!(3, add_instruction.rd.get_id());
        assert_eq!(2, add_instruction.rs1.get_id());
        assert_eq!(1, add_instruction.rs2.get_id());
        assert_eq!(RegisterType::Group, add_instruction.rd.get_type());
        assert_eq!(RegisterType::Group, add_instruction.rs1.get_type());
        assert_eq!(RegisterType::Group, add_instruction.rs2.get_type());

        let (_, add_instruction) = Add::new("add sf.r3, sf.r2, sf.r1;").unwrap();
        assert_eq!(3, add_instruction.rd.get_id());
        assert_eq!(2, add_instruction.rs1.get_id());
        assert_eq!(1, add_instruction.rs2.get_id());
        assert_eq!(RegisterType::ScalarField, add_instruction.rd.get_type());
        assert_eq!(RegisterType::ScalarField, add_instruction.rs1.get_type());
        assert_eq!(RegisterType::ScalarField, add_instruction.rs2.get_type());
    }

    #[test]
    fn test_malformed_add() {
        todo!()
    }
}
