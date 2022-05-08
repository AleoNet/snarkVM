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
    function::{parsers::*, Instruction, Opcode, Operation, Register, Registers},
    Program,
    Value,
};

use snarkvm_circuits::{
    count,
    Count,
    Field,
    Group,
    Literal,
    LiteralType,
    Metrics,
    Parser,
    ParserResult,
    SubChecked,
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

use core::{fmt, ops::Sub as SubCircuit};
use nom::combinator::map;
use std::io::{Read, Result as IoResult, Write};

/// Computes `first - second`, storing the outcome in `destination`.
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
            Value::Definition(name, ..) => P::halt(format!("{name} is not a literal")),
        };
        let second = match registers.load(self.operation.second()) {
            Value::Literal(literal) => literal,
            Value::Definition(name, ..) => P::halt(format!("{name} is not a literal")),
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

impl<P: Program> Metrics<Self> for Sub<P> {
    type Case = (LiteralType<P::Environment>, LiteralType<P::Environment>);

    fn count(case: &Self::Case) -> Count {
        crate::match_count!(match SubCircuit::count(case) {
            (Field, Field) => Field,
            (Group, Group) => Group,
            (I8, I8) => I8,
            (I16, I16) => I16,
            (I32, I32) => I32,
            (I64, I64) => I64,
            (I128, I128) => I128,
            (U8, U8) => U8,
            (U16, U16) => U16,
            (U32, U32) => U32,
            (U64, U64) => U64,
            (U128, U128) => U128,
        })
    }
}

impl<P: Program> Parser for Sub<P> {
    type Environment = P::Environment;

    /// Parses a string into a 'sub' operation.
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
    use crate::{test_instruction_halts, test_modes, Identifier, Process};

    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<Process>::parse("sub r0 r1 into r2;").unwrap();
        assert!(matches!(instruction, Instruction::Sub(_)));
    }

    test_modes!(field, Sub, "3field", "2field", "1field");

    mod group {
        use super::*;
        use crate::binary_instruction_test;

        // 2group - 0group has special output mode behavior.
        // Normally, a public variable minus a constant would yield a private variable. However, since
        // the constant is zero, we return the original public variable.
        binary_instruction_test!(
            constant_and_constant_yields_constant,
            Sub,
            "2group.constant",
            "0group.constant",
            "2group.constant"
        );
        binary_instruction_test!(
            constant_and_public_yields_private,
            Sub,
            "2group.constant",
            "0group.public",
            "2group.private"
        );
        binary_instruction_test!(
            constant_and_private_yields_private,
            Sub,
            "2group.constant",
            "0group.private",
            "2group.private"
        );
        binary_instruction_test!(
            public_and_constant_yields_public,
            Sub,
            "2group.public",
            "0group.constant",
            "2group.public"
        );
        binary_instruction_test!(
            private_and_constant_yields_private,
            Sub,
            "2group.private",
            "0group.constant",
            "2group.private"
        );
        binary_instruction_test!(
            public_and_public_yields_private,
            Sub,
            "2group.public",
            "0group.public",
            "2group.private"
        );
        binary_instruction_test!(
            public_and_private_yields_private,
            Sub,
            "2group.public",
            "0group.private",
            "2group.private"
        );
        binary_instruction_test!(
            private_and_public_yields_private,
            Sub,
            "2group.private",
            "0group.public",
            "2group.private"
        );
        binary_instruction_test!(
            private_and_private_yields_private,
            Sub,
            "2group.private",
            "0group.private",
            "2group.private"
        );
    }

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

    test_instruction_halts!(
        i8_underflow_halts,
        Sub,
        "Integer underflow on subtraction of two constants",
        &format!("{}i8.constant", i8::MIN),
        "1i8.constant"
    );
    test_instruction_halts!(
        i16_underflow_halts,
        Sub,
        "Integer underflow on subtraction of two constants",
        &format!("{}i16.constant", i16::MIN),
        "1i16.constant"
    );
    test_instruction_halts!(
        i32_underflow_halts,
        Sub,
        "Integer underflow on subtraction of two constants",
        &format!("{}i32.constant", i32::MIN),
        "1i32.constant"
    );
    test_instruction_halts!(
        i64_underflow_halts,
        Sub,
        "Integer underflow on subtraction of two constants",
        &format!("{}i64.constant", i64::MIN),
        "1i64.constant"
    );
    test_instruction_halts!(
        i128_underflow_halts,
        Sub,
        "Integer underflow on subtraction of two constants",
        &format!("{}i128.constant", i128::MIN),
        "1i128.constant"
    );
    test_instruction_halts!(
        u8_underflow_halts,
        Sub,
        "Integer underflow on subtraction of two constants",
        &format!("{}u8.constant", u8::MIN),
        "1u8.constant"
    );
    test_instruction_halts!(
        u16_underflow_halts,
        Sub,
        "Integer underflow on subtraction of two constants",
        &format!("{}u16.constant", u16::MIN),
        "1u16.constant"
    );
    test_instruction_halts!(
        u32_underflow_halts,
        Sub,
        "Integer underflow on subtraction of two constants",
        &format!("{}u32.constant", u32::MIN),
        "1u32.constant"
    );
    test_instruction_halts!(
        u64_underflow_halts,
        Sub,
        "Integer underflow on subtraction of two constants",
        &format!("{}u64.constant", u64::MIN),
        "1u64.constant"
    );
    test_instruction_halts!(
        u128_underflow_halts,
        Sub,
        "Integer underflow on subtraction of two constants",
        &format!("{}u128.constant", u128::MIN),
        "1u128.constant"
    );

    test_instruction_halts!(
        address_halts,
        Sub,
        "Invalid 'sub' instruction",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.constant",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.constant"
    );
    test_instruction_halts!(boolean_halts, Sub, "Invalid 'sub' instruction", "true.constant", "true.constant");
    test_instruction_halts!(string_halts, Sub, "Invalid 'sub' instruction", "\"hello\".constant", "\"world\".constant");

    #[test]
    #[should_panic(expected = "message is not a literal")]
    fn test_definition_halts() {
        let first = Value::<Process>::Definition(Identifier::from_str("message"), vec![
            Value::from_str("2group.public"),
            Value::from_str("10field.private"),
        ]);
        let second = first.clone();

        let registers = Registers::<Process>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.define(&Register::from_str("r2"));
        registers.assign(&Register::from_str("r0"), first);
        registers.assign(&Register::from_str("r1"), second);

        Sub::from_str("r0 r1 into r2").evaluate(&registers);
    }
}
