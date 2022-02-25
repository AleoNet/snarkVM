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

use crate::{Immediate, Opcode, ParserResult, Type};

use core::num::ParseIntError;
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{char, one_of},
    combinator::{map, recognize},
    multi::{many0, many1},
    sequence::terminated,
};

// TODO: Documentation
pub struct Operation {
    opcode: Opcode,
    typ: Type,
}

impl Operation {
    pub fn new(input: &str) -> ParserResult<Operation> {
        let (input, opcode) = Opcode::new(input)?;
        let (input, _) = tag(".")(input)?;
        let (input, typ) = Type::new(input)?;
        Ok((input, Self { opcode, typ }))
    }

    pub fn get_opcode(&self) -> Opcode {
        self.opcode
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_operation_new() {
        let (_, operation) = Operation::new("add.base").unwrap();
        assert_eq!(operation.opcode, Opcode::Add);
        assert_eq!(operation.typ, Type::BaseField);

        let (_, operation) = Operation::new("addc.u8").unwrap();
        assert_eq!(operation.opcode, Opcode::AddChecked);
        assert_eq!(operation.typ, Type::U8);

        let (_, operation) = Operation::new("addw.i8").unwrap();
        assert_eq!(operation.opcode, Opcode::AddWrapped);
        assert_eq!(operation.typ, Type::I8);

        let (_, operation) = Operation::new("and.bool").unwrap();
        assert_eq!(operation.opcode, Opcode::And);
        assert_eq!(operation.typ, Type::Boolean);

        let (_, operation) = Operation::new("eq.group").unwrap();
        assert_eq!(operation.opcode, Opcode::Eq);
        assert_eq!(operation.typ, Type::Group);

        let (_, operation) = Operation::new("sub.u128").unwrap();
        assert_eq!(operation.opcode, Opcode::Sub);
        assert_eq!(operation.typ, Type::U128);

        let (_, operation) = Operation::new("subc.u16").unwrap();
        assert_eq!(operation.opcode, Opcode::SubChecked);
        assert_eq!(operation.typ, Type::U16);

        let (_, operation) = Operation::new("subw.i16").unwrap();
        assert_eq!(operation.opcode, Opcode::SubWrapped);
        assert_eq!(operation.typ, Type::I16);

        let (_, operation) = Operation::new("ter.scalar").unwrap();
        assert_eq!(operation.opcode, Opcode::Ternary);
        assert_eq!(operation.typ, Type::ScalarField);
    }

    #[test]
    fn test_invalid_operation() {
        assert!(Operation::new("jal.u8").is_err());
        assert!(Operation::new("sub.vector").is_err());
    }
}
