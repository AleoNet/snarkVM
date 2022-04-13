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

/// Performs a bitwise Or on `first` and `second`, storing the outcome in `destination`.
pub struct Or<P: Program> {
    operation: BinaryOperation<P>,
}

impl<P: Program> Or<P> {
    /// Returns the operands of the instruction.
    pub fn operands(&self) -> Vec<Operand<P>> {
        self.operation.operands()
    }

    /// Returns the destination register of the instruction.
    pub fn destination(&self) -> &Register<P> {
        self.operation.destination()
    }
}

impl<P: Program> Opcode for Or<P> {
    /// Returns the opcode as a string.
    #[inline]
    fn opcode() -> &'static str {
        "or"
    }
}

impl<P: Program> Operation<P> for Or<P> {
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
            (Literal::Boolean(a), Literal::Boolean(b)) => Literal::Boolean(a | b),
            (Literal::I8(a), Literal::I8(b)) => Literal::I8(a | b),
            (Literal::I16(a), Literal::I16(b)) => Literal::I16(a | b),
            (Literal::I32(a), Literal::I32(b)) => Literal::I32(a | b),
            (Literal::I64(a), Literal::I64(b)) => Literal::I64(a | b),
            (Literal::I128(a), Literal::I128(b)) => Literal::I128(a | b),
            (Literal::U8(a), Literal::U8(b)) => Literal::U8(a | b),
            (Literal::U16(a), Literal::U16(b)) => Literal::U16(a | b),
            (Literal::U32(a), Literal::U32(b)) => Literal::U32(a | b),
            (Literal::U64(a), Literal::U64(b)) => Literal::U64(a | b),
            (Literal::U128(a), Literal::U128(b)) => Literal::U128(a | b),
            _ => P::halt(format!("Invalid '{}' instruction", Self::opcode())),
        };

        registers.assign(self.operation.destination(), result);
    }
}

impl<P: Program> Parser for Or<P> {
    type Environment = P::Environment;

    /// Parses a string into an 'or' operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the operation from the string.
        let (string, operation) = map(BinaryOperation::parse, |operation| Self { operation })(string)?;
        // Return the operation.
        Ok((string, operation))
    }
}

impl<P: Program> fmt::Display for Or<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.operation)
    }
}

impl<P: Program> FromBytes for Or<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self { operation: BinaryOperation::read_le(&mut reader)? })
    }
}

impl<P: Program> ToBytes for Or<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.operation.write_le(&mut writer)
    }
}

#[allow(clippy::from_over_into)]
impl<P: Program> Into<Instruction<P>> for Or<P> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<P> {
        Instruction::Or(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{test_instruction_halts, test_modes, Identifier, Process};

    const BOOLEAN_MODE_TESTS: [[&str; 3]; 9] = [
        ["public", "public", "private"],
        ["public", "constant", "public"],
        ["public", "private", "private"],
        ["private", "public", "private"],
        ["private", "constant", "private"],
        ["private", "private", "private"],
        ["constant", "public", "constant"],
        ["constant", "constant", "constant"],
        ["constant", "private", "constant"],
    ];

    const INTEGER_MODE_TESTS: [[&str; 3]; 9] = [
        ["public", "public", "private"],
        ["public", "constant", "public"],
        ["public", "private", "private"],
        ["private", "public", "private"],
        ["private", "constant", "private"],
        ["private", "private", "private"],
        ["constant", "public", "public"],
        ["constant", "constant", "constant"],
        ["constant", "private", "private"],
    ];

    test_modes!(boolean, Or, "true", "false", "true", BOOLEAN_MODE_TESTS);
    test_modes!(i8, Or, "1i8", "0i8", "1i8", INTEGER_MODE_TESTS);
    test_modes!(i16, Or, "1i16", "0i16", "1i16", INTEGER_MODE_TESTS);
    test_modes!(i32, Or, "1i32", "0i32", "1i32", INTEGER_MODE_TESTS);
    test_modes!(i64, Or, "1i64", "0i64", "1i64", INTEGER_MODE_TESTS);
    test_modes!(i128, Or, "1i128", "0i128", "1i128", INTEGER_MODE_TESTS);
    test_modes!(u8, Or, "1u8", "2u8", "3u8", INTEGER_MODE_TESTS);
    test_modes!(u16, Or, "1u16", "2u16", "3u16", INTEGER_MODE_TESTS);
    test_modes!(u32, Or, "1u32", "2u32", "3u32", INTEGER_MODE_TESTS);
    test_modes!(u64, Or, "1u64", "2u64", "3u64", INTEGER_MODE_TESTS);
    test_modes!(u128, Or, "1u128", "2u128", "3u128", INTEGER_MODE_TESTS);

    test_instruction_halts!(
        address_halts,
        Or,
        "Invalid 'or' instruction",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.constant",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.constant"
    );
    test_instruction_halts!(string_halts, Or, "Invalid 'or' instruction", "\"hello\".constant", "\"world\".constant");
    test_instruction_halts!(field_halts, Or, "Invalid 'or' instruction", "1field.constant", "1field.constant");
    test_instruction_halts!(group_halts, Or, "Invalid 'or' instruction", "2group.constant", "2group.constant");
    test_instruction_halts!(scalar_halts, Or, "Invalid 'or' instruction", "1scalar.constant", "1scalar.constant");

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

        Or::from_str("r0 r1 into r2").evaluate(&registers);
    }
}
