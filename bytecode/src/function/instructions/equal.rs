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
    LiteralType,
    Program,
    Value,
};
use snarkvm_circuits::{
    count,
    Boolean,
    Count,
    Equal as CircuitEqual,
    Field,
    Literal,
    Metrics,
    Parser,
    ParserResult,
    I8,
    U8,
};
use snarkvm_utilities::{FromBytes, ToBytes};

use core::fmt;
use nom::combinator::map;
use std::io::{Read, Result as IoResult, Write};

/// Checks that `first` is equal to `second`, storing the outcome in `destination`.
pub struct Equal<P: Program> {
    operation: BinaryOperation<P>,
}

impl<P: Program> Equal<P> {
    /// Returns the operands of the instruction.
    pub fn operands(&self) -> Vec<Operand<P>> {
        self.operation.operands()
    }

    /// Returns the destination register of the instruction.
    pub fn destination(&self) -> &Register<P> {
        self.operation.destination()
    }
}

impl<P: Program> Opcode for Equal<P> {
    /// Returns the opcode as a string.
    #[inline]
    fn opcode() -> &'static str {
        "eq"
    }
}

impl<P: Program> Operation<P> for Equal<P> {
    /// Evaluates the operation.
    #[inline]
    fn evaluate(&self, registers: &Registers<P>) {
        // Load the values for the first and second operands.
        let first = match registers.load(self.operation.first()) {
            Value::Literal(literal) => literal,
            Value::Definition(name, ..) => P::halt(format!("{name} is not a literal")),
        };
        let second = match registers.load(self.operation.second()) {
            Value::Literal(literal) => literal,
            Value::Definition(name, ..) => P::halt(format!("{name} is not a literal")),
        };

        // Perform the operation.
        let result = match (first, second) {
            (Literal::Address(a), Literal::Address(b)) => Literal::Boolean(a.is_equal(&b)),
            (Literal::Boolean(a), Literal::Boolean(b)) => Literal::Boolean(a.is_equal(&b)),
            (Literal::Field(a), Literal::Field(b)) => Literal::Boolean(a.is_equal(&b)),
            (Literal::Group(a), Literal::Group(b)) => Literal::Boolean(a.is_equal(&b)),
            (Literal::I8(a), Literal::I8(b)) => Literal::Boolean(a.is_equal(&b)),
            (Literal::I16(a), Literal::I16(b)) => Literal::Boolean(a.is_equal(&b)),
            (Literal::I32(a), Literal::I32(b)) => Literal::Boolean(a.is_equal(&b)),
            (Literal::I64(a), Literal::I64(b)) => Literal::Boolean(a.is_equal(&b)),
            (Literal::I128(a), Literal::I128(b)) => Literal::Boolean(a.is_equal(&b)),
            (Literal::Scalar(a), Literal::Scalar(b)) => Literal::Boolean(a.is_equal(&b)),
            (Literal::U8(a), Literal::U8(b)) => Literal::Boolean(a.is_equal(&b)),
            (Literal::U16(a), Literal::U16(b)) => Literal::Boolean(a.is_equal(&b)),
            (Literal::U32(a), Literal::U32(b)) => Literal::Boolean(a.is_equal(&b)),
            (Literal::U64(a), Literal::U64(b)) => Literal::Boolean(a.is_equal(&b)),
            (Literal::U128(a), Literal::U128(b)) => Literal::Boolean(a.is_equal(&b)),
            _ => P::halt(format!("Invalid '{}' instruction", Self::opcode())),
        };

        registers.assign(self.operation.destination(), result);
    }
}

impl<P: Program> Metrics<Self> for Equal<P> {
    type Case = (LiteralType<P>, LiteralType<P>);

    fn count(case: &Self::Case) -> Count {
        match case {
            (LiteralType::Field(mode_a), LiteralType::Field(mode_b)) => count!(
                Field<P::Environment>,
                CircuitEqual<Field<P::Environment>, Output = Boolean<P::Environment>>,
                &(*mode_a, *mode_b)
            ),
            (LiteralType::I8(mode_a), LiteralType::I8(mode_b)) => {
                count!(
                    I8<P::Environment>,
                    CircuitEqual<I8<P::Environment>, Output = Boolean<P::Environment>>,
                    &(*mode_a, *mode_b)
                )
            }
            (LiteralType::U8(mode_a), LiteralType::U8(mode_b)) => {
                count!(
                    U8<P::Environment>,
                    CircuitEqual<U8<P::Environment>, Output = Boolean<P::Environment>>,
                    &(*mode_a, *mode_b)
                )
            }
            _ => P::halt(format!("Invalid '{}' instruction", Self::opcode())),
        }
    }
}

impl<P: Program> Parser for Equal<P> {
    type Environment = P::Environment;

    /// Parses a string into an 'Equal' operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the operation from the string.
        map(BinaryOperation::parse, |operation| Self { operation })(string)
    }
}

impl<P: Program> fmt::Display for Equal<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.operation)
    }
}

impl<P: Program> FromBytes for Equal<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self { operation: BinaryOperation::read_le(&mut reader)? })
    }
}

impl<P: Program> ToBytes for Equal<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.operation.write_le(&mut writer)
    }
}

#[allow(clippy::from_over_into)]
impl<P: Program> Into<Instruction<P>> for Equal<P> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<P> {
        Instruction::Equal(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{binary_instruction_test, test_instruction_halts, test_modes, Identifier, Process, Register};

    const BOOLEAN_MODE_TESTS: [[&str; 3]; 9] = [
        ["public", "public", "private"],
        ["public", "constant", "public"],
        ["public", "private", "private"],
        ["private", "constant", "private"],
        ["private", "public", "private"],
        ["private", "private", "private"],
        ["constant", "private", "private"],
        ["constant", "public", "public"],
        ["constant", "constant", "constant"],
    ];

    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<Process>::parse("eq r0 r1 into r2;").unwrap();
        assert!(matches!(instruction, Instruction::Equal(_)));
    }

    test_modes!(
        address,
        Equal,
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
        "true"
    );
    binary_instruction_test!(
        address_ne,
        Equal,
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.public",
        "aleo1t9r2aalldn3al4346l3pdplj8prrz5svvahsrl64gp4023342sxsrhs2yg.public",
        "false.private"
    );

    test_modes!(boolean, Equal, "true", "true", "true", BOOLEAN_MODE_TESTS);
    binary_instruction_test!(boolean_ne, Equal, "true.public", "false.public", "false.private");

    test_modes!(field, Equal, "1field", "1field", "true");
    binary_instruction_test!(field_ne, Equal, "1field.public", "2field.public", "false.private");

    test_modes!(group, Equal, "2group", "2group", "true");
    binary_instruction_test!(group_ne, Equal, "2group.public", "0group.public", "false.private");

    test_modes!(i8, Equal, "1i8", "1i8", "true");
    binary_instruction_test!(i8_ne, Equal, "1i8.public", "2i8.public", "false.private");

    test_modes!(i16, Equal, "1i16", "1i16", "true");
    binary_instruction_test!(i16_ne, Equal, "1i16.public", "2i16.public", "false.private");

    test_modes!(i32, Equal, "1i32", "1i32", "true");
    binary_instruction_test!(i32_ne, Equal, "1i32.public", "2i32.public", "false.private");

    test_modes!(i64, Equal, "1i64", "1i64", "true");
    binary_instruction_test!(i64_ne, Equal, "1i64.public", "2i64.public", "false.private");

    test_modes!(i128, Equal, "1i128", "1i128", "true");
    binary_instruction_test!(i128_ne, Equal, "1i128.public", "2i128.public", "false.private");

    test_modes!(scalar, Equal, "1scalar", "1scalar", "true");
    binary_instruction_test!(scalar_ne, Equal, "1scalar.public", "2scalar.public", "false.private");

    test_modes!(u8, Equal, "1u8", "1u8", "true");
    binary_instruction_test!(u8_ne, Equal, "1u8.public", "2u8.public", "false.private");

    test_modes!(u16, Equal, "1u16", "1u16", "true");
    binary_instruction_test!(u16_ne, Equal, "1u16.public", "2u16.public", "false.private");

    test_modes!(u32, Equal, "1u32", "1u32", "true");
    binary_instruction_test!(u32_ne, Equal, "1u32.public", "2u32.public", "false.private");

    test_modes!(u64, Equal, "1u64", "1u64", "true");
    binary_instruction_test!(u64_ne, Equal, "1u64.public", "2u64.public", "false.private");

    test_modes!(u128, Equal, "1u128", "1u128", "true");
    binary_instruction_test!(u128_ne, Equal, "1u128.public", "2u128.public", "false.private");

    test_instruction_halts!(string_halts, Equal, "Invalid 'eq' instruction", "\"hello\"", "\"hello\"");

    #[test]
    #[should_panic(expected = "message is not a literal")]
    fn test_composite_halts() {
        let first = Value::<Process>::Definition(Identifier::from_str("message"), vec![
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

        Equal::from_str("r0 r1 into r2").evaluate(&registers);
    }
}
