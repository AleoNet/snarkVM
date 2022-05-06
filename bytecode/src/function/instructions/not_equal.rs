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
use snarkvm_circuits::{Equal, Literal, Parser, ParserResult};
use snarkvm_utilities::{FromBytes, ToBytes};

use core::fmt;
use nom::combinator::map;
use std::io::{Read, Result as IoResult, Write};

/// Returns true if `first` is not equal to `second`, storing the result in `destination`.
pub struct NotEqual<P: Program> {
    operation: BinaryOperation<P>,
}

impl<P: Program> NotEqual<P> {
    /// Returns the operands of the instruction.
    pub fn operands(&self) -> Vec<Operand<P>> {
        self.operation.operands()
    }

    /// Returns the destination register of the instruction.
    pub fn destination(&self) -> &Register<P> {
        self.operation.destination()
    }
}

impl<P: Program> Opcode for NotEqual<P> {
    /// Returns the opcode as a string.
    #[inline]
    fn opcode() -> &'static str {
        "neq"
    }
}

impl<P: Program> Operation<P> for NotEqual<P> {
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
            (Literal::Address(a), Literal::Address(b)) => Literal::Boolean(a.is_not_equal(&b)),
            (Literal::Boolean(a), Literal::Boolean(b)) => Literal::Boolean(a.is_not_equal(&b)),
            (Literal::Field(a), Literal::Field(b)) => Literal::Boolean(a.is_not_equal(&b)),
            (Literal::Group(a), Literal::Group(b)) => Literal::Boolean(a.is_not_equal(&b)),
            (Literal::I8(a), Literal::I8(b)) => Literal::Boolean(a.is_not_equal(&b)),
            (Literal::I16(a), Literal::I16(b)) => Literal::Boolean(a.is_not_equal(&b)),
            (Literal::I32(a), Literal::I32(b)) => Literal::Boolean(a.is_not_equal(&b)),
            (Literal::I64(a), Literal::I64(b)) => Literal::Boolean(a.is_not_equal(&b)),
            (Literal::I128(a), Literal::I128(b)) => Literal::Boolean(a.is_not_equal(&b)),
            (Literal::Scalar(a), Literal::Scalar(b)) => Literal::Boolean(a.is_not_equal(&b)),
            (Literal::U8(a), Literal::U8(b)) => Literal::Boolean(a.is_not_equal(&b)),
            (Literal::U16(a), Literal::U16(b)) => Literal::Boolean(a.is_not_equal(&b)),
            (Literal::U32(a), Literal::U32(b)) => Literal::Boolean(a.is_not_equal(&b)),
            (Literal::U64(a), Literal::U64(b)) => Literal::Boolean(a.is_not_equal(&b)),
            (Literal::U128(a), Literal::U128(b)) => Literal::Boolean(a.is_not_equal(&b)),
            _ => P::halt(format!("Invalid '{}' instruction", Self::opcode())),
        };

        registers.assign(self.operation.destination(), result);
    }
}

impl<P: Program> Parser for NotEqual<P> {
    type Environment = P::Environment;

    /// Parses a string into an 'eq' operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the operation from the string.
        let (string, operation) = map(BinaryOperation::parse, |operation| Self { operation })(string)?;
        // Return the operation.
        Ok((string, operation))
    }
}

impl<P: Program> fmt::Display for NotEqual<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.operation)
    }
}

impl<P: Program> FromBytes for NotEqual<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self { operation: BinaryOperation::read_le(&mut reader)? })
    }
}

impl<P: Program> ToBytes for NotEqual<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.operation.write_le(&mut writer)
    }
}

#[allow(clippy::from_over_into)]
impl<P: Program> Into<Instruction<P>> for NotEqual<P> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<P> {
        Instruction::NotEqual(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{binary_instruction_test, test_instruction_halts, test_modes, Identifier, Process};

    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<Process>::parse("neq r0 r1 into r2;").unwrap();
        assert!(matches!(instruction, Instruction::NotEqual(_)));
    }

    test_modes!(
        address,
        NotEqual,
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
        "false"
    );
    binary_instruction_test!(
        address_ne,
        NotEqual,
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.public",
        "aleo1t9r2aalldn3al4346l3pdplj8prrz5svvahsrl64gp4023342sxsrhs2yg.public",
        "true.private"
    );

    test_modes!(boolean, NotEqual, "true", "true", "false");
    binary_instruction_test!(boolean_ne, NotEqual, "true.public", "false.public", "true.private");

    test_modes!(field, NotEqual, "1field", "1field", "false");
    binary_instruction_test!(field_ne, NotEqual, "1field.public", "2field.public", "true.private");

    test_modes!(group, NotEqual, "2group", "2group", "false");
    binary_instruction_test!(group_ne, NotEqual, "2group.public", "0group.public", "true.private");

    test_modes!(i8, NotEqual, "1i8", "1i8", "false");
    binary_instruction_test!(i8_ne, NotEqual, "1i8.public", "-1i8.public", "true.private");

    test_modes!(i16, NotEqual, "1i16", "1i16", "false");
    binary_instruction_test!(i16_ne, NotEqual, "1i16.public", "-1i16.public", "true.private");

    test_modes!(i32, NotEqual, "1i32", "1i32", "false");
    binary_instruction_test!(i32_ne, NotEqual, "1i32.public", "-1i32.public", "true.private");

    test_modes!(i64, NotEqual, "1i64", "1i64", "false");
    binary_instruction_test!(i64_ne, NotEqual, "1i64.public", "-1i64.public", "true.private");

    test_modes!(i128, NotEqual, "1i128", "1i128", "false");
    binary_instruction_test!(i128_ne, NotEqual, "1i128.public", "-1i128.public", "true.private");

    test_modes!(scalar, NotEqual, "1scalar", "1scalar", "false");
    binary_instruction_test!(scalar_ne, NotEqual, "1scalar.public", "-1scalar.public", "true.private");

    test_modes!(u8, NotEqual, "1u8", "1u8", "false");
    binary_instruction_test!(u8_ne, NotEqual, "1u8.public", "2u8.public", "true.private");

    test_modes!(u16, NotEqual, "1u16", "1u16", "false");
    binary_instruction_test!(u16_ne, NotEqual, "1u16.public", "2u16.public", "true.private");

    test_modes!(u32, NotEqual, "1u32", "1u32", "false");
    binary_instruction_test!(u32_ne, NotEqual, "1u32.public", "2u32.public", "true.private");

    test_modes!(u64, NotEqual, "1u64", "1u64", "false");
    binary_instruction_test!(u64_ne, NotEqual, "1u64.public", "2u64.public", "true.private");

    test_modes!(u128, NotEqual, "1u128", "1u128", "false");
    binary_instruction_test!(u128_ne, NotEqual, "1u128.public", "2u128.public", "true.private");

    test_instruction_halts!(string_halts, NotEqual, "Invalid 'neq' instruction", "\"hello\"", "\"hello\"");

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

        NotEqual::from_str("r0 r1 into r2").evaluate(&registers);
    }
}
