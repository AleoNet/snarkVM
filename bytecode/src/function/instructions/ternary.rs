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
use snarkvm_circuits::{
    Boolean,
    Field,
    Group,
    Literal,
    Parser,
    ParserResult,
    Scalar,
    Ternary as TernaryCircuit,
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
use snarkvm_utilities::{FromBytes, ToBytes};

use core::fmt;
use nom::combinator::map;
use std::io::{Read, Result as IoResult, Write};

/// Selects `first`, if `condition` is true, otherwise selects `second`, storing the result in `destination`.
pub struct Ternary<P: Program> {
    operation: TernaryOperation<P>,
}

impl<P: Program> Ternary<P> {
    /// Returns the operands of the instruction.
    pub fn operands(&self) -> Vec<Operand<P>> {
        self.operation.operands()
    }

    /// Returns the destination register of the instruction.
    pub fn destination(&self) -> &Register<P> {
        self.operation.destination()
    }
}

impl<P: Program> Opcode for Ternary<P> {
    /// Returns the opcode as a string.
    #[inline]
    fn opcode() -> &'static str {
        "ter"
    }
}

impl<P: Program> Operation<P> for Ternary<P> {
    /// Evaluates the operation.
    #[inline]
    fn evaluate(&self, registers: &Registers<P>) {
        // Load the values for the condition, first, and second operands.
        let condition = match registers.load(self.operation.condition()) {
            Value::Literal(literal) => literal,
            Value::Composite(name, ..) => P::halt(format!("{name} is not a literal")),
        };
        let first = match registers.load(self.operation.first()) {
            Value::Literal(literal) => literal,
            Value::Composite(name, ..) => P::halt(format!("{name} is not a literal")),
        };
        let second = match registers.load(self.operation.second()) {
            Value::Literal(literal) => literal,
            Value::Composite(name, ..) => P::halt(format!("{name} is not a literal")),
        };

        // Perform the operation.
        let result = match (condition, first, second) {
            (Literal::Boolean(condition), Literal::Boolean(a), Literal::Boolean(b)) => {
                Literal::Boolean(Boolean::ternary(&condition, &a, &b))
            }
            (Literal::Boolean(condtition), Literal::Field(a), Literal::Field(b)) => {
                Literal::Field(Field::ternary(&condtition, &a, &b))
            }
            (Literal::Boolean(condition), Literal::Group(a), Literal::Group(b)) => {
                Literal::Group(Group::ternary(&condition, &a, &b))
            }
            (Literal::Boolean(condition), Literal::I8(a), Literal::I8(b)) => {
                Literal::I8(I8::ternary(&condition, &a, &b))
            }
            (Literal::Boolean(condition), Literal::I16(a), Literal::I16(b)) => {
                Literal::I16(I16::ternary(&condition, &a, &b))
            }
            (Literal::Boolean(condition), Literal::I32(a), Literal::I32(b)) => {
                Literal::I32(I32::ternary(&condition, &a, &b))
            }
            (Literal::Boolean(condition), Literal::I64(a), Literal::I64(b)) => {
                Literal::I64(I64::ternary(&condition, &a, &b))
            }
            (Literal::Boolean(condition), Literal::I128(a), Literal::I128(b)) => {
                Literal::I128(I128::ternary(&condition, &a, &b))
            }
            (Literal::Boolean(condition), Literal::U8(a), Literal::U8(b)) => {
                Literal::U8(U8::ternary(&condition, &a, &b))
            }
            (Literal::Boolean(condition), Literal::U16(a), Literal::U16(b)) => {
                Literal::U16(U16::ternary(&condition, &a, &b))
            }
            (Literal::Boolean(condition), Literal::U32(a), Literal::U32(b)) => {
                Literal::U32(U32::ternary(&condition, &a, &b))
            }
            (Literal::Boolean(condition), Literal::U64(a), Literal::U64(b)) => {
                Literal::U64(U64::ternary(&condition, &a, &b))
            }
            (Literal::Boolean(condition), Literal::U128(a), Literal::U128(b)) => {
                Literal::U128(U128::ternary(&condition, &a, &b))
            }
            (Literal::Boolean(condition), Literal::Scalar(a), Literal::Scalar(b)) => {
                Literal::Scalar(Scalar::ternary(&condition, &a, &b))
            }
            _ => P::halt(format!("Invalid '{}' instruction", Self::opcode())),
        };

        registers.assign(self.operation.destination(), result);
    }
}

impl<P: Program> Parser for Ternary<P> {
    type Environment = P::Environment;

    /// Parses a string into a 'ter' operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        map(TernaryOperation::parse, |operation| Self { operation })(string)
    }
}

impl<P: Program> fmt::Display for Ternary<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.operation)
    }
}

impl<P: Program> FromBytes for Ternary<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self { operation: TernaryOperation::read_le(&mut reader)? })
    }
}

impl<P: Program> ToBytes for Ternary<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.operation.write_le(&mut writer)
    }
}

#[allow(clippy::from_over_into)]
impl<P: Program> Into<Instruction<P>> for Ternary<P> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<P> {
        Instruction::Ternary(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Identifier, Process, Register};

    type P = Process;

    fn ternary_test(condition: &str, a: &str, b: &str, expected: &str) {
        let condition = Value::<P>::from_str(condition);
        let first = Value::<P>::from_str(a);
        let second = Value::<P>::from_str(b);
        let expected = Value::<P>::from_str(expected);

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.define(&Register::from_str("r2"));
        registers.define(&Register::from_str("r3"));
        registers.assign(&Register::from_str("r0"), condition);
        registers.assign(&Register::from_str("r1"), first);
        registers.assign(&Register::from_str("r2"), second);

        Ternary::from_str("r0 r1 r2 into r3").evaluate(&registers);
        let candidate = registers.load(&Register::from_str("r3"));
        assert_eq!(expected, candidate);
    }

    #[test]
    fn test_boolean() {
        ternary_test("true.private", "true.private", "false.private", "true.private");
        ternary_test("false.private", "true.private", "false.private", "false.private");
    }

    #[test]
    fn test_field() {
        ternary_test("true.private", "1field.private", "2field.private", "1field.private");
        ternary_test("false.private", "1field.private", "2field.private", "2field.private");
    }

    #[test]
    fn test_group() {
        ternary_test("true.private", "0group.private", "2group.private", "0group.private");
        ternary_test("false.private", "0group.private", "2group.private", "2group.private");
    }

    #[test]
    fn test_i8() {
        ternary_test("true.private", "1i8.private", "-1i8.private", "1i8.private");
        ternary_test("false.private", "1i8.private", "-1i8.private", "-1i8.private");
    }

    #[test]
    fn test_i16() {
        ternary_test("true.private", "1i16.private", "-1i16.private", "1i16.private");
        ternary_test("false.private", "1i16.private", "-1i16.private", "-1i16.private");
    }

    #[test]
    fn test_i32() {
        ternary_test("true.private", "1i32.private", "-1i32.private", "1i32.private");
        ternary_test("false.private", "1i32.private", "-1i32.private", "-1i32.private");
    }

    #[test]
    fn test_i64() {
        ternary_test("true.private", "1i64.private", "-1i64.private", "1i64.private");
        ternary_test("false.private", "1i64.private", "-1i64.private", "-1i64.private");
    }

    #[test]
    fn test_i128() {
        ternary_test("true.private", "1i128.private", "-1i128.private", "1i128.private");
        ternary_test("false.private", "1i128.private", "-1i128.private", "-1i128.private");
    }

    #[test]
    fn test_u8() {
        ternary_test("true.private", "1u8.private", "2u8.private", "1u8.private");
        ternary_test("false.private", "1u8.private", "2u8.private", "2u8.private");
    }

    #[test]
    fn test_u16() {
        ternary_test("true.private", "1u16.private", "2u16.private", "1u16.private");
        ternary_test("false.private", "1u16.private", "2u16.private", "2u16.private");
    }

    #[test]
    fn test_u32() {
        ternary_test("true.private", "1u32.private", "2u32.private", "1u32.private");
        ternary_test("false.private", "1u32.private", "2u32.private", "2u32.private");
    }

    #[test]
    fn test_u64() {
        ternary_test("true.private", "1u64.private", "2u64.private", "1u64.private");
        ternary_test("false.private", "1u64.private", "2u64.private", "2u64.private");
    }

    #[test]
    fn test_u128() {
        ternary_test("true.private", "1u128.private", "2u128.private", "1u128.private");
        ternary_test("false.private", "1u128.private", "2u128.private", "2u128.private");
    }

    #[test]
    fn test_scalar() {
        ternary_test("true.private", "1scalar.private", "2scalar.private", "1scalar.private");
        ternary_test("false.private", "1scalar.private", "2scalar.private", "2scalar.private");
    }

    #[test]
    #[should_panic(expected = "Invalid 'ter' instruction")]
    fn test_ternary_halts_on_mismatched_operand_types() {
        ternary_test("true.private", "1scalar.private", "1field.private", "\"unreachable\".private");
    }

    #[test]
    #[should_panic(expected = "message is not a literal")]
    fn test_composite_halts() {
        let condition = Value::<P>::from_str("true.public");
        let first = Value::<P>::Composite(Identifier::from_str("message"), vec![
            Literal::from_str("2group.public"),
            Literal::from_str("10field.private"),
        ]);
        let second = first.clone();

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.define(&Register::from_str("r2"));
        registers.define(&Register::from_str("r3"));
        registers.assign(&Register::from_str("r0"), condition);
        registers.assign(&Register::from_str("r1"), first);
        registers.assign(&Register::from_str("r2"), second);

        Ternary::from_str("r0 r1 r2 into r3").evaluate(&registers);
    }
}
