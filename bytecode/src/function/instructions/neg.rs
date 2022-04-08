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

use crate::{
    function::{parsers::*, Instruction, Opcode, Operation, Registers},
    helpers::Register,
    Program,
    Value,
};
use snarkvm_circuits::{Literal, Parser, ParserResult};
use snarkvm_utilities::{FromBytes, ToBytes};

use core::fmt;
use nom::combinator::map;
use std::io::{Read, Result as IoResult, Write};

/// Negates `first`, storing the outcome in `destination`.
pub struct Neg<P: Program> {
    operation: UnaryOperation<P>,
}

impl<P: Program> Neg<P> {
    /// Returns the operands of the instruction.
    pub fn operands(&self) -> Vec<Operand<P>> {
        self.operation.operands()
    }

    /// Returns the destination register of the instruction.
    pub fn destination(&self) -> &Register<P> {
        self.operation.destination()
    }
}

impl<P: Program> Opcode for Neg<P> {
    /// Returns the opcode as a string.
    #[inline]
    fn opcode() -> &'static str {
        "neg"
    }
}

impl<P: Program> Operation<P> for Neg<P> {
    /// Evaluates the operation.
    #[inline]
    fn evaluate(&self, registers: &Registers<P>) {
        // Load the values for the first and second operands.
        let first = match registers.load(self.operation.first()) {
            Value::Literal(literal) => literal,
            Value::Composite(name, ..) => P::halt(format!("{name} is not a literal")),
        };

        // Perform the operation.
        let result = match first {
            Literal::Field(a) => Literal::Field(-a),
            Literal::Group(a) => Literal::Group(-a),
            Literal::I8(a) => Literal::I8(-a),
            Literal::I16(a) => Literal::I16(-a),
            Literal::I32(a) => Literal::I32(-a),
            Literal::I64(a) => Literal::I64(-a),
            Literal::I128(a) => Literal::I128(-a),
            _ => P::halt(format!("Invalid '{}' instruction", Self::opcode())),
        };

        registers.assign(self.operation.destination(), result);
    }
}

impl<P: Program> Parser for Neg<P> {
    type Environment = P::Environment;

    /// Parses a string into an 'neg' operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the operation from the string.
        map(UnaryOperation::parse, |operation| Self { operation })(string)
    }
}

impl<P: Program> fmt::Display for Neg<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.operation)
    }
}

impl<P: Program> FromBytes for Neg<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self { operation: UnaryOperation::read_le(&mut reader)? })
    }
}

impl<P: Program> ToBytes for Neg<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.operation.write_le(&mut writer)
    }
}

#[allow(clippy::from_over_into)]
impl<P: Program> Into<Instruction<P>> for Neg<P> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<P> {
        Instruction::Neg(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::unary_instruction_test;

    mod modes {
        use super::Neg;
        use crate::test_modes;

        test_modes!(field, Neg, "1field", "-1field");
        test_modes!(group, Neg, "2group", "-2group");
        test_modes!(i8, Neg, "1i8", "-1i8");
        test_modes!(i16, Neg, "1i16", "-1i16");
        test_modes!(i32, Neg, "1i32", "-1i32");
        test_modes!(i64, Neg, "1i64", "-1i64");
        test_modes!(i128, Neg, "1i128", "-1i128");
    }

    unary_instruction_test!(field, Neg, "1field.private", "-1field.private");
    unary_instruction_test!(group, Neg, "2group.private", "-2group.private");
    unary_instruction_test!(i8, Neg, "1i8.private", "-1i8.private");
    unary_instruction_test!(i16, Neg, "1i16.private", "-1i16.private");
    unary_instruction_test!(i32, Neg, "1i32.private", "-1i32.private");
    unary_instruction_test!(i64, Neg, "1i64.private", "-1i64.private");
    unary_instruction_test!(i128, Neg, "1i128.private", "-1i128.private");
}
