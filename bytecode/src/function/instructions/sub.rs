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
use snarkvm_circuits::{Literal, Parser, ParserResult, SubChecked};
use snarkvm_utilities::{FromBytes, ToBytes};

use core::fmt;
use nom::combinator::map;
use std::io::{Read, Result as IoResult, Write};

/// Subtracts `first` from `second`, storing the outcome in `destination`.
pub struct Sub<P: Program> {
    operation: BinaryOperation<P>,
}

impl<P: Program> Sub<P> {
    /// Returns the operands of the instruction.
    pub fn operands(&self) -> Vec<Operand<P>> {
        self.operation.operands()
    }

    /// Returns the destination register of the instruction.
    pub fn destination(&self) -> &Register<P> {
        self.operation.destination()
    }
}

impl<P: Program> Opcode for Sub<P> {
    /// Returns the opcode as a string.
    #[inline]
    fn opcode() -> &'static str {
        "sub"
    }
}

impl<P: Program> Operation<P> for Sub<P> {
    /// Evaluates the operation.
    #[inline]
    fn evaluate(&self, registers: &Registers<P>) {
        // Load the values for the first and second operands.
        let first = match registers.load(self.operation.first()) {
            Value::Literal(literal) => literal,
            Value::Composite(name, ..) => P::halt(format!("{name} is not a literal")),
        };
        let second = match registers.load(self.operation.second()) {
            Value::Literal(literal) => literal,
            Value::Composite(name, ..) => P::halt(format!("{name} is not a literal")),
        };

        // Perform the operation.
        let result = match (first, second) {
            (Literal::Field(a), Literal::Field(b)) => Literal::Field(a - b),
            (Literal::Group(a), Literal::Group(b)) => Literal::Group(a - b),
            (Literal::I8(a), Literal::I8(b)) => Literal::I8(a.sub_checked(&b)),
            (Literal::I16(a), Literal::I16(b)) => Literal::I16(a.sub_checked(&b)),
            (Literal::I32(a), Literal::I32(b)) => Literal::I32(a.sub_checked(&b)),
            (Literal::I64(a), Literal::I64(b)) => Literal::I64(a.sub_checked(&b)),
            (Literal::I128(a), Literal::I128(b)) => Literal::I128(a.sub_checked(&b)),
            (Literal::U8(a), Literal::U8(b)) => Literal::U8(a.sub_checked(&b)),
            (Literal::U16(a), Literal::U16(b)) => Literal::U16(a.sub_checked(&b)),
            (Literal::U32(a), Literal::U32(b)) => Literal::U32(a.sub_checked(&b)),
            (Literal::U64(a), Literal::U64(b)) => Literal::U64(a.sub_checked(&b)),
            (Literal::U128(a), Literal::U128(b)) => Literal::U128(a.sub_checked(&b)),
            _ => P::halt(format!("Invalid '{}' instruction", Self::opcode())),
        };

        registers.assign(self.operation.destination(), result);
    }
}

impl<P: Program> Parser for Sub<P> {
    type Environment = P::Environment;

    /// Parses a string into an 'sub' operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the operation from the string.
        let (string, operation) = map(BinaryOperation::parse, |operation| Self { operation })(string)?;
        // Return the operation.
        Ok((string, operation))
    }
}

impl<P: Program> fmt::Display for Sub<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.operation)
    }
}

impl<P: Program> FromBytes for Sub<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self { operation: BinaryOperation::read_le(&mut reader)? })
    }
}

impl<P: Program> ToBytes for Sub<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.operation.write_le(&mut writer)
    }
}

#[allow(clippy::from_over_into)]
impl<P: Program> Into<Instruction<P>> for Sub<P> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<P> {
        Instruction::Sub(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_modes;

    test_modes!(field, Sub, "3field", "2field", "1field");
    test_modes!(group, Sub, "2group", "0group", "2group");
    test_modes!(i8, Sub, "1i8", "2i8", "-1i8");
    test_modes!(i16, Sub, "1i16", "2i16", "-1i16");
    test_modes!(i32, Sub, "1i32", "2i32", "-1i32");
    test_modes!(i64, Sub, "1i64", "2i64", "-1i64");
    test_modes!(i128, Sub, "1i128", "2i128", "-1i128");
    test_modes!(u8, Sub, "3u8", "2u8", "1u8");
    test_modes!(u16, Sub, "3u16", "2u16", "1u16");
    test_modes!(u32, Sub, "3u32", "2u32", "1u32");
    test_modes!(u64, Sub, "3u64", "2u64", "1u64");
    test_modes!(u128, Sub, "3u128", "2u128", "1u128");
}
