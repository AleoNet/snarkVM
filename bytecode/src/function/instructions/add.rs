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
use snarkvm_circuits::{AddChecked, Literal, Parser, ParserResult};
use snarkvm_utilities::{FromBytes, ToBytes};

use core::fmt;
use nom::combinator::map;
use std::io::{Read, Result as IoResult, Write};

/// Adds `first` with `second`, storing the outcome in `destination`.
pub struct Add<P: Program> {
    operation: BinaryOperation<P>,
}

impl<P: Program> Add<P> {
    /// Returns the operands of the instruction.
    pub fn operands(&self) -> Vec<Operand<P>> {
        self.operation.operands()
    }

    /// Returns the destination register of the instruction.
    pub fn destination(&self) -> &Register<P> {
        self.operation.destination()
    }
}

impl<P: Program> Opcode for Add<P> {
    /// Returns the opcode as a string.
    #[inline]
    fn opcode() -> &'static str {
        "add"
    }
}

impl<P: Program> Operation<P> for Add<P> {
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
            (Literal::Field(a), Literal::Field(b)) => Literal::Field(a + b),
            (Literal::Group(a), Literal::Group(b)) => Literal::Group(a + b),
            (Literal::I8(a), Literal::I8(b)) => Literal::I8(a.add_checked(&b)),
            (Literal::I16(a), Literal::I16(b)) => Literal::I16(a.add_checked(&b)),
            (Literal::I32(a), Literal::I32(b)) => Literal::I32(a.add_checked(&b)),
            (Literal::I64(a), Literal::I64(b)) => Literal::I64(a.add_checked(&b)),
            (Literal::I128(a), Literal::I128(b)) => Literal::I128(a.add_checked(&b)),
            (Literal::U8(a), Literal::U8(b)) => Literal::U8(a.add_checked(&b)),
            (Literal::U16(a), Literal::U16(b)) => Literal::U16(a.add_checked(&b)),
            (Literal::U32(a), Literal::U32(b)) => Literal::U32(a.add_checked(&b)),
            (Literal::U64(a), Literal::U64(b)) => Literal::U64(a.add_checked(&b)),
            (Literal::U128(a), Literal::U128(b)) => Literal::U128(a.add_checked(&b)),
            (Literal::Scalar(a), Literal::Scalar(b)) => Literal::Scalar(a + b),
            _ => P::halt(format!("Invalid '{}' instruction", Self::opcode())),
        };

        registers.assign(self.operation.destination(), result);
    }
}

impl<P: Program> Parser for Add<P> {
    type Environment = P::Environment;

    /// Parses a string into an 'add' operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the operation from the string.
        map(BinaryOperation::parse, |operation| Self { operation })(string)
    }
}

impl<P: Program> fmt::Display for Add<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.operation)
    }
}

impl<P: Program> FromBytes for Add<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self { operation: BinaryOperation::read_le(&mut reader)? })
    }
}

impl<P: Program> ToBytes for Add<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.operation.write_le(&mut writer)
    }
}

#[allow(clippy::from_over_into)]
impl<P: Program> Into<Instruction<P>> for Add<P> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<P> {
        Instruction::Add(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Identifier, Process, Register};

    type P = Process;

    fn check_add_test(first: Value<P>, second: Value<P>, expected: Value<P>) {
        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.define(&Register::from_str("r2"));
        registers.assign(&Register::from_str("r0"), first);
        registers.assign(&Register::from_str("r1"), second);

        Add::from_str("r0 r1 into r2").evaluate(&registers);
        let candidate = registers.load(&Register::from_str("r2"));
        assert_eq!(expected, candidate);
    }

    #[test]
    fn test_add_field() {
        let one = Value::<P>::from_str("1field.public");
        let two = Value::<P>::from_str("2field.private");
        let three = Value::<P>::from_str("3field.private");
        check_add_test(one, two, three);
    }

    #[test]
    fn test_add_group() {
        let two = Value::<P>::from_str("2group.private");
        let zero = Value::<P>::from_str("0group.private");
        check_add_test(two.clone(), zero, two);
    }

    #[test]
    fn test_add_scalar() {
        let one = Value::<P>::from_str("1scalar.public");
        let two = Value::<P>::from_str("2scalar.private");
        let three = Value::<P>::from_str("3scalar.private");
        check_add_test(one, two, three);
    }

    #[test]
    fn test_add_i8() {
        let negative_one = Value::<P>::from_str("-1i8.public");
        let two = Value::<P>::from_str("2i8.private");
        let one = Value::<P>::from_str("1i8.private");
        check_add_test(negative_one, two, one);
    }

    #[test]
    #[should_panic(expected = "Integer overflow on addition of two constants")]
    fn test_add_i8_constant_overflow_halts() {
        let max = Value::<P>::from_str(&format!("{}i8.constant", i8::MAX));
        let one = Value::<P>::from_str("1i8.constant");
        let unreachable = Value::<P>::from_str("\"Unreachable\".constant");
        check_add_test(max, one, unreachable);
    }

    #[test]
    fn test_add_i16() {
        let negative_one = Value::<P>::from_str("-1i16.public");
        let two = Value::<P>::from_str("2i16.private");
        let one = Value::<P>::from_str("1i16.private");
        check_add_test(negative_one, two, one);
    }

    #[test]
    #[should_panic(expected = "Integer overflow on addition of two constants")]
    fn test_add_i16_constant_overflow_halts() {
        let max = Value::<P>::from_str(&format!("{}i16.constant", i16::MAX));
        let one = Value::<P>::from_str("1i16.constant");
        let unreachable = Value::<P>::from_str("\"Unreachable\".constant");
        check_add_test(max, one, unreachable);
    }

    #[test]
    fn test_add_i32() {
        let negative_one = Value::<P>::from_str("-1i32.public");
        let two = Value::<P>::from_str("2i32.private");
        let one = Value::<P>::from_str("1i32.private");
        check_add_test(negative_one, two, one);
    }

    #[test]
    #[should_panic(expected = "Integer overflow on addition of two constants")]
    fn test_add_i32_constant_overflow_halts() {
        let max = Value::<P>::from_str(&format!("{}i32.constant", i32::MAX));
        let one = Value::<P>::from_str("1i32.constant");
        let unreachable = Value::<P>::from_str("\"Unreachable\".constant");
        check_add_test(max, one, unreachable);
    }

    #[test]
    fn test_add_i64() {
        let negative_one = Value::<P>::from_str("-1i64.public");
        let two = Value::<P>::from_str("2i64.private");
        let one = Value::<P>::from_str("1i64.private");
        check_add_test(negative_one, two, one);
    }

    #[test]
    #[should_panic(expected = "Integer overflow on addition of two constants")]
    fn test_add_i64_constant_overflow_halts() {
        let max = Value::<P>::from_str(&format!("{}i64.constant", i64::MAX));
        let one = Value::<P>::from_str("1i64.constant");
        let unreachable = Value::<P>::from_str("\"Unreachable\".constant");
        check_add_test(max, one, unreachable);
    }

    #[test]
    fn test_add_i128() {
        let negative_one = Value::<P>::from_str("-1i128.public");
        let two = Value::<P>::from_str("2i128.private");
        let one = Value::<P>::from_str("1i128.private");
        check_add_test(negative_one, two, one);
    }

    #[test]
    #[should_panic(expected = "Integer overflow on addition of two constants")]
    fn test_add_i128_constant_overflow_halts() {
        let max = Value::<P>::from_str(&format!("{}i128.constant", i128::MAX));
        let one = Value::<P>::from_str("1i128.constant");
        let unreachable = Value::<P>::from_str("\"Unreachable\".constant");
        check_add_test(max, one, unreachable);
    }

    #[test]
    fn test_add_u8() {
        let one = Value::<P>::from_str("1u8.public");
        let two = Value::<P>::from_str("2u8.private");
        let three = Value::<P>::from_str("3u8.private");
        check_add_test(one, two, three);
    }

    #[test]
    #[should_panic(expected = "Integer overflow on addition of two constants")]
    fn test_add_u8_constant_overflow_halts() {
        let max = Value::<P>::from_str(&format!("{}u8.constant", u8::MAX));
        let one = Value::<P>::from_str("1u8.constant");
        let unreachable = Value::<P>::from_str("\"Unreachable\".constant");
        check_add_test(max, one, unreachable);
    }

    #[test]
    fn test_add_u16() {
        let one = Value::<P>::from_str("1u16.public");
        let two = Value::<P>::from_str("2u16.private");
        let three = Value::<P>::from_str("3u16.private");
        check_add_test(one, two, three);
    }

    #[test]
    #[should_panic(expected = "Integer overflow on addition of two constants")]
    fn test_add_u16_constant_overflow_halts() {
        let max = Value::<P>::from_str(&format!("{}u16.constant", u16::MAX));
        let one = Value::<P>::from_str("1u16.constant");
        let unreachable = Value::<P>::from_str("\"Unreachable\".constant");
        check_add_test(max, one, unreachable);
    }

    #[test]
    fn test_add_u32() {
        let one = Value::<P>::from_str("1u32.public");
        let two = Value::<P>::from_str("2u32.private");
        let three = Value::<P>::from_str("3u32.private");
        check_add_test(one, two, three);
    }

    #[test]
    #[should_panic(expected = "Integer overflow on addition of two constants")]
    fn test_add_u32_constant_overflow_halts() {
        let max = Value::<P>::from_str(&format!("{}u32.constant", u32::MAX));
        let one = Value::<P>::from_str("1u32.constant");
        let unreachable = Value::<P>::from_str("\"Unreachable\".constant");
        check_add_test(max, one, unreachable);
    }

    #[test]
    fn test_add_u64() {
        let one = Value::<P>::from_str("1u64.public");
        let two = Value::<P>::from_str("2u64.private");
        let three = Value::<P>::from_str("3u64.private");
        check_add_test(one, two, three);
    }

    #[test]
    #[should_panic(expected = "Integer overflow on addition of two constants")]
    fn test_add_u64_constant_overflow_halts() {
        let max = Value::<P>::from_str(&format!("{}u64.constant", u64::MAX));
        let one = Value::<P>::from_str("1u64.constant");
        let unreachable = Value::<P>::from_str("\"Unreachable\".constant");
        check_add_test(max, one, unreachable);
    }

    #[test]
    fn test_add_u128() {
        let one = Value::<P>::from_str("1u128.public");
        let two = Value::<P>::from_str("2u128.private");
        let three = Value::<P>::from_str("3u128.private");
        check_add_test(one, two, three);
    }

    #[test]
    #[should_panic(expected = "Integer overflow on addition of two constants")]
    fn test_add_u128_constant_overflow_halts() {
        let max = Value::<P>::from_str(&format!("{}u128.constant", u128::MAX));
        let one = Value::<P>::from_str("1u128.constant");
        let unreachable = Value::<P>::from_str("\"Unreachable\".constant");
        check_add_test(max, one, unreachable);
    }

    #[test]
    #[should_panic(expected = "message is not a literal")]
    fn test_halts_on_composite() {
        let composite = Value::<P>::Composite(Identifier::from_str("message"), vec![
            Literal::from_str("2group.public"),
            Literal::from_str("10field.private"),
        ]);
        let second = Value::<P>::from_str("4scalar.public");
        let unreachable = Value::<P>::from_str("\"Unreachable\".constant");

        check_add_test(composite, second, unreachable);
    }

    #[test]
    #[should_panic(expected = "Invalid 'add' instruction")]
    fn test_halts_on_string_operand() {
        let invalid_add_literal = Value::<P>::from_str("\"hello world\".public");
        let second = Value::<P>::from_str("4scalar.public");
        let unreachable = Value::<P>::from_str("\"Unreachable\".constant");

        check_add_test(invalid_add_literal, second, unreachable);
    }

    #[test]
    #[should_panic(expected = "Invalid 'add' instruction")]
    fn test_halts_on_address_operand() {
        let invalid_add_literal =
            Value::<P>::from_str("aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.public");
        let second = Value::<P>::from_str("4scalar.public");
        let unreachable = Value::<P>::from_str("\"Unreachable\".constant");

        check_add_test(invalid_add_literal, second, unreachable);
    }

    #[test]
    #[should_panic(expected = "Invalid 'add' instruction")]
    fn test_halts_on_boolean_operand() {
        let invalid_add_literal = Value::<P>::from_str("true.public");
        let second = Value::<P>::from_str("4scalar.public");
        let unreachable = Value::<P>::from_str("\"Unreachable\".constant");

        check_add_test(invalid_add_literal, second, unreachable);
    }
}
