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

/// Performs a bitwise Xor on `first` and `second`, storing the outcome in `destination`.
pub struct Xor<P: Program> {
    operation: BinaryOperation<P>,
}

impl<P: Program> Xor<P> {
    /// Returns the operands of the instruction.
    pub fn operands(&self) -> Vec<Operand<P>> {
        self.operation.operands()
    }

    /// Returns the destination register of the instruction.
    pub fn destination(&self) -> &Register<P> {
        self.operation.destination()
    }
}

impl<P: Program> Opcode for Xor<P> {
    /// Returns the opcode as a string.
    #[inline]
    fn opcode() -> &'static str {
        "xor"
    }
}

impl<P: Program> Operation<P> for Xor<P> {
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
            (Literal::Boolean(a), Literal::Boolean(b)) => Literal::Boolean(a ^ b),
            (Literal::I8(a), Literal::I8(b)) => Literal::I8(a ^ b),
            (Literal::I16(a), Literal::I16(b)) => Literal::I16(a ^ b),
            (Literal::I32(a), Literal::I32(b)) => Literal::I32(a ^ b),
            (Literal::I64(a), Literal::I64(b)) => Literal::I64(a ^ b),
            (Literal::I128(a), Literal::I128(b)) => Literal::I128(a ^ b),
            (Literal::U8(a), Literal::U8(b)) => Literal::U8(a ^ b),
            (Literal::U16(a), Literal::U16(b)) => Literal::U16(a ^ b),
            (Literal::U32(a), Literal::U32(b)) => Literal::U32(a ^ b),
            (Literal::U64(a), Literal::U64(b)) => Literal::U64(a ^ b),
            (Literal::U128(a), Literal::U128(b)) => Literal::U128(a ^ b),
            _ => P::halt(format!("Invalid '{}' instruction", Self::opcode())),
        };

        registers.assign(self.operation.destination(), result);
    }
}

impl<P: Program> Parser for Xor<P> {
    type Environment = P::Environment;

    /// Parses a string into an 'xor' operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the operation from the string.
        let (string, operation) = map(BinaryOperation::parse, |operation| Self { operation })(string)?;
        // Return the operation.
        Ok((string, operation))
    }
}

impl<P: Program> fmt::Display for Xor<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.operation)
    }
}

impl<P: Program> FromBytes for Xor<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self { operation: BinaryOperation::read_le(&mut reader)? })
    }
}

impl<P: Program> ToBytes for Xor<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.operation.write_le(&mut writer)
    }
}

#[allow(clippy::from_over_into)]
impl<P: Program> Into<Instruction<P>> for Xor<P> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<P> {
        Instruction::Xor(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{test_instruction_halts, test_modes, Identifier, Process};

    const SIGNED_INTEGER_MODE_TESTS: [[&str; 3]; 9] = [
        ["public", "public", "private"],
        ["public", "constant", "public"],
        ["public", "private", "private"],
        ["private", "public", "private"],
        ["private", "constant", "private"],
        ["private", "private", "private"],
        ["constant", "public", "private"],
        ["constant", "constant", "constant"],
        ["constant", "private", "private"],
    ];

    const UNSIGNED_INTEGER_MODE_TESTS: [[&str; 3]; 9] = [
        ["public", "public", "private"],
        ["public", "constant", "private"],
        ["public", "private", "private"],
        ["private", "public", "private"],
        ["private", "constant", "private"],
        ["private", "private", "private"],
        ["constant", "public", "private"],
        ["constant", "constant", "constant"],
        ["constant", "private", "private"],
    ];

    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<Process>::parse("xor r0 r1 into r2;").unwrap();
        assert!(matches!(instruction, Instruction::Xor(_)));
    }

    // Boolean happens to produce the same modes as signed integers for Xor.
    test_modes!(boolean, Xor, "true", "false", "true", SIGNED_INTEGER_MODE_TESTS);
    test_modes!(i8, Xor, "1i8", "0i8", "1i8", SIGNED_INTEGER_MODE_TESTS);
    test_modes!(i16, Xor, "1i16", "0i16", "1i16", SIGNED_INTEGER_MODE_TESTS);
    test_modes!(i32, Xor, "1i32", "0i32", "1i32", SIGNED_INTEGER_MODE_TESTS);
    test_modes!(i64, Xor, "1i64", "0i64", "1i64", SIGNED_INTEGER_MODE_TESTS);
    test_modes!(i128, Xor, "1i128", "0i128", "1i128", SIGNED_INTEGER_MODE_TESTS);
    test_modes!(u8, Xor, "1u8", "2u8", "3u8", UNSIGNED_INTEGER_MODE_TESTS);
    test_modes!(u16, Xor, "1u16", "2u16", "3u16", UNSIGNED_INTEGER_MODE_TESTS);
    test_modes!(u32, Xor, "1u32", "2u32", "3u32", UNSIGNED_INTEGER_MODE_TESTS);
    test_modes!(u64, Xor, "1u64", "2u64", "3u64", UNSIGNED_INTEGER_MODE_TESTS);
    test_modes!(u128, Xor, "1u128", "2u128", "3u128", UNSIGNED_INTEGER_MODE_TESTS);

    test_instruction_halts!(
        address_halts,
        Xor,
        "Invalid 'xor' instruction",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.constant",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.constant"
    );
    test_instruction_halts!(string_halts, Xor, "Invalid 'xor' instruction", "\"hello\".constant", "\"world\".constant");
    test_instruction_halts!(field_halts, Xor, "Invalid 'xor' instruction", "1field.constant", "1field.constant");
    test_instruction_halts!(group_halts, Xor, "Invalid 'xor' instruction", "2group.constant", "2group.constant");
    test_instruction_halts!(scalar_halts, Xor, "Invalid 'xor' instruction", "1scalar.constant", "1scalar.constant");

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

        Xor::from_str("r0 r1 into r2").evaluate(&registers);
    }
}
