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
use snarkvm_circuits::{Compare, Literal, Parser, ParserResult};
use snarkvm_utilities::{FromBytes, ToBytes};

use core::fmt;
use nom::combinator::map;
use std::io::{Read, Result as IoResult, Write};

/// Checks if `first` is less than or equal to `second`, storing the outcome in `destination`.
pub struct LessThanOrEqual<P: Program> {
    operation: BinaryOperation<P>,
}

impl<P: Program> LessThanOrEqual<P> {
    /// Returns the operands of the instruction.
    pub fn operands(&self) -> Vec<Operand<P>> {
        self.operation.operands()
    }

    /// Returns the destination register of the instruction.
    pub fn destination(&self) -> &Register<P> {
        self.operation.destination()
    }
}

impl<P: Program> Opcode for LessThanOrEqual<P> {
    /// Returns the opcode as a string.
    #[inline]
    fn opcode() -> &'static str {
        "lte"
    }
}

impl<P: Program> Operation<P> for LessThanOrEqual<P> {
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
            (Literal::Field(a), Literal::Field(b)) => Literal::Boolean(a.is_less_than_or_equal(&b)),
            (Literal::I8(a), Literal::I8(b)) => Literal::Boolean(a.is_less_than_or_equal(&b)),
            (Literal::I16(a), Literal::I16(b)) => Literal::Boolean(a.is_less_than_or_equal(&b)),
            (Literal::I32(a), Literal::I32(b)) => Literal::Boolean(a.is_less_than_or_equal(&b)),
            (Literal::I64(a), Literal::I64(b)) => Literal::Boolean(a.is_less_than_or_equal(&b)),
            (Literal::I128(a), Literal::I128(b)) => Literal::Boolean(a.is_less_than_or_equal(&b)),
            (Literal::Scalar(a), Literal::Scalar(b)) => Literal::Boolean(a.is_less_than_or_equal(&b)),
            (Literal::U8(a), Literal::U8(b)) => Literal::Boolean(a.is_less_than_or_equal(&b)),
            (Literal::U16(a), Literal::U16(b)) => Literal::Boolean(a.is_less_than_or_equal(&b)),
            (Literal::U32(a), Literal::U32(b)) => Literal::Boolean(a.is_less_than_or_equal(&b)),
            (Literal::U64(a), Literal::U64(b)) => Literal::Boolean(a.is_less_than_or_equal(&b)),
            (Literal::U128(a), Literal::U128(b)) => Literal::Boolean(a.is_less_than_or_equal(&b)),
            _ => P::halt(format!("Invalid '{}' instruction", Self::opcode())),
        };

        registers.assign(self.operation.destination(), result);
    }
}

impl<P: Program> Parser for LessThanOrEqual<P> {
    type Environment = P::Environment;

    /// Parses a string into an 'lte' operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the operation from the string.
        let (string, operation) = map(BinaryOperation::parse, |operation| Self { operation })(string)?;
        // Return the operation.
        Ok((string, operation))
    }
}

impl<P: Program> fmt::Display for LessThanOrEqual<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.operation)
    }
}

impl<P: Program> FromBytes for LessThanOrEqual<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self { operation: BinaryOperation::read_le(&mut reader)? })
    }
}

impl<P: Program> ToBytes for LessThanOrEqual<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.operation.write_le(&mut writer)
    }
}

#[allow(clippy::from_over_into)]
impl<P: Program> Into<Instruction<P>> for LessThanOrEqual<P> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<P> {
        Instruction::LessThanOrEqual(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{test_instruction_halts, test_modes, Identifier, Process};

    test_modes!(field, LessThanOrEqual, "2field", "2field", "true");
    test_modes!(i8, LessThanOrEqual, "1i8", "1i8", "true");
    test_modes!(i16, LessThanOrEqual, "1i16", "1i16", "true");
    test_modes!(i32, LessThanOrEqual, "1i32", "1i32", "true");
    test_modes!(i64, LessThanOrEqual, "1i64", "1i64", "true");
    test_modes!(i128, LessThanOrEqual, "1i128", "1i128", "true");
    test_modes!(scalar, LessThanOrEqual, "2scalar", "2scalar", "true");
    test_modes!(u8, LessThanOrEqual, "1u8", "1u8", "true");
    test_modes!(u16, LessThanOrEqual, "1u16", "1u16", "true");
    test_modes!(u32, LessThanOrEqual, "1u32", "1u32", "true");
    test_modes!(u64, LessThanOrEqual, "1u64", "1u64", "true");
    test_modes!(u128, LessThanOrEqual, "1u128", "1u128", "true");

    test_instruction_halts!(
        address_halts,
        LessThanOrEqual,
        "Invalid 'lte' instruction",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.constant",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.constant"
    );
    test_instruction_halts!(
        boolean_halts,
        LessThanOrEqual,
        "Invalid 'lte' instruction",
        "true.constant",
        "true.constant"
    );
    test_instruction_halts!(group_halts, LessThanOrEqual, "Invalid 'lte' instruction", "0group", "2group");
    test_instruction_halts!(string_halts, LessThanOrEqual, "Invalid 'lte' instruction", "\"hello\"", "\"hello\"");

    #[test]
    #[should_panic(expected = "message is not a literal")]
    fn test_composite_halts() {
        let first = Value::<Process>::Composite(Identifier::from_str("message"), vec![
            Literal::from_str("2group.public"),
            Literal::from_str("10field.private"),
        ]);
        let second = first.clone();

        let registers = Registers::<Process>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.define(&Register::from_str("r2"));
        registers.assign(&Register::from_str("r0"), first);
        registers.assign(&Register::from_str("r1"), second);

        LessThanOrEqual::from_str("r0 r1 into r2").evaluate(&registers);
    }
}
