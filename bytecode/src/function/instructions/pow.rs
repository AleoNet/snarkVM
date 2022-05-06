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
use snarkvm_circuits::{Literal, Parser, ParserResult, Pow as PowCircuit, PowChecked};
use snarkvm_utilities::{FromBytes, ToBytes};

use core::fmt;
use nom::combinator::map;
use std::io::{Read, Result as IoResult, Write};

/// Raises `first` to the power of `second`, storing the outcome in `destination`.
pub struct Pow<P: Program> {
    operation: BinaryOperation<P>,
}

impl<P: Program> Pow<P> {
    /// Returns the operands of the instruction.
    pub fn operands(&self) -> Vec<Operand<P>> {
        self.operation.operands()
    }

    /// Returns the destination register of the instruction.
    pub fn destination(&self) -> &Register<P> {
        self.operation.destination()
    }
}

impl<P: Program> Opcode for Pow<P> {
    /// Returns the opcode as a string.
    #[inline]
    fn opcode() -> &'static str {
        "pow"
    }
}

impl<P: Program> Operation<P> for Pow<P> {
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
            (Literal::Field(a), Literal::Field(b)) => Literal::Field(a.pow(b)),
            (Literal::I8(a), Literal::U8(b)) => Literal::I8(a.pow_checked(&b)),
            (Literal::I8(a), Literal::U16(b)) => Literal::I8(a.pow_checked(&b)),
            (Literal::I8(a), Literal::U32(b)) => Literal::I8(a.pow_checked(&b)),
            (Literal::I16(a), Literal::U8(b)) => Literal::I16(a.pow_checked(&b)),
            (Literal::I16(a), Literal::U16(b)) => Literal::I16(a.pow_checked(&b)),
            (Literal::I16(a), Literal::U32(b)) => Literal::I16(a.pow_checked(&b)),
            (Literal::I32(a), Literal::U8(b)) => Literal::I32(a.pow_checked(&b)),
            (Literal::I32(a), Literal::U16(b)) => Literal::I32(a.pow_checked(&b)),
            (Literal::I32(a), Literal::U32(b)) => Literal::I32(a.pow_checked(&b)),
            (Literal::I64(a), Literal::U8(b)) => Literal::I64(a.pow_checked(&b)),
            (Literal::I64(a), Literal::U16(b)) => Literal::I64(a.pow_checked(&b)),
            (Literal::I64(a), Literal::U32(b)) => Literal::I64(a.pow_checked(&b)),
            (Literal::I128(a), Literal::U8(b)) => Literal::I128(a.pow_checked(&b)),
            (Literal::I128(a), Literal::U16(b)) => Literal::I128(a.pow_checked(&b)),
            (Literal::I128(a), Literal::U32(b)) => Literal::I128(a.pow_checked(&b)),
            (Literal::U8(a), Literal::U8(b)) => Literal::U8(a.pow_checked(&b)),
            (Literal::U8(a), Literal::U16(b)) => Literal::U8(a.pow_checked(&b)),
            (Literal::U8(a), Literal::U32(b)) => Literal::U8(a.pow_checked(&b)),
            (Literal::U16(a), Literal::U8(b)) => Literal::U16(a.pow_checked(&b)),
            (Literal::U16(a), Literal::U16(b)) => Literal::U16(a.pow_checked(&b)),
            (Literal::U16(a), Literal::U32(b)) => Literal::U16(a.pow_checked(&b)),
            (Literal::U32(a), Literal::U8(b)) => Literal::U32(a.pow_checked(&b)),
            (Literal::U32(a), Literal::U16(b)) => Literal::U32(a.pow_checked(&b)),
            (Literal::U32(a), Literal::U32(b)) => Literal::U32(a.pow_checked(&b)),
            (Literal::U64(a), Literal::U8(b)) => Literal::U64(a.pow_checked(&b)),
            (Literal::U64(a), Literal::U16(b)) => Literal::U64(a.pow_checked(&b)),
            (Literal::U64(a), Literal::U32(b)) => Literal::U64(a.pow_checked(&b)),
            (Literal::U128(a), Literal::U8(b)) => Literal::U128(a.pow_checked(&b)),
            (Literal::U128(a), Literal::U16(b)) => Literal::U128(a.pow_checked(&b)),
            (Literal::U128(a), Literal::U32(b)) => Literal::U128(a.pow_checked(&b)),
            _ => P::halt(format!("Invalid '{}' instruction", Self::opcode())),
        };

        registers.assign(self.operation.destination(), result);
    }
}

impl<P: Program> Parser for Pow<P> {
    type Environment = P::Environment;

    /// Parses a string into a 'pow' operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the operation from the string.
        let (string, operation) = map(BinaryOperation::parse, |operation| Self { operation })(string)?;
        // Return the operation.
        Ok((string, operation))
    }
}

impl<P: Program> fmt::Display for Pow<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.operation)
    }
}

impl<P: Program> FromBytes for Pow<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self { operation: BinaryOperation::read_le(&mut reader)? })
    }
}

impl<P: Program> ToBytes for Pow<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.operation.write_le(&mut writer)
    }
}

#[allow(clippy::from_over_into)]
impl<P: Program> Into<Instruction<P>> for Pow<P> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<P> {
        Instruction::Pow(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{binary_instruction_test, test_instruction_halts, test_modes, Identifier, Process, Register};

    type P = Process;

    test_modes!(field, Pow, "2field", "2field", "4field");
    binary_instruction_test!(field_pow_1, Pow, "2field.public", "1field.public", "2field.private");
    binary_instruction_test!(field_pow_0, Pow, "2field.public", "0field.public", "1field.private");

    test_modes!(i8_pow_u8, Pow, "2i8", "2u8", "4i8");
    test_modes!(i8_pow_u16, Pow, "2i8", "2u16", "4i8");
    test_modes!(i8_pow_u32, Pow, "2i8", "2u32", "4i8");

    test_modes!(i16_pow_u8, Pow, "2i16", "2u8", "4i16");
    test_modes!(i16_pow_u16, Pow, "2i16", "2u16", "4i16");
    test_modes!(i16_pow_u32, Pow, "2i16", "2u32", "4i16");

    test_modes!(i32_pow_u8, Pow, "2i32", "2u8", "4i32");
    test_modes!(i32_pow_u16, Pow, "2i32", "2u16", "4i32");
    test_modes!(i32_pow_u32, Pow, "2i32", "2u32", "4i32");

    test_modes!(i64_pow_u8, Pow, "2i64", "2u8", "4i64");
    test_modes!(i64_pow_u16, Pow, "2i64", "2u16", "4i64");
    test_modes!(i64_pow_u32, Pow, "2i64", "2u32", "4i64");

    test_modes!(i128_pow_u8, Pow, "2i128", "2u8", "4i128");
    test_modes!(i128_pow_u16, Pow, "2i128", "2u16", "4i128");
    test_modes!(i128_pow_u32, Pow, "2i128", "2u32", "4i128");

    test_modes!(u8_pow_u8, Pow, "2u8", "2u8", "4u8");
    test_modes!(u8_pow_u16, Pow, "2u8", "2u16", "4u8");
    test_modes!(u8_pow_u32, Pow, "2u8", "2u32", "4u8");

    test_modes!(u16_pow_u8, Pow, "2u16", "2u8", "4u16");
    test_modes!(u16_pow_u16, Pow, "2u16", "2u16", "4u16");
    test_modes!(u16_pow_u32, Pow, "2u16", "2u32", "4u16");

    test_modes!(u32_pow_u8, Pow, "2u32", "2u8", "4u32");
    test_modes!(u32_pow_u16, Pow, "2u32", "2u16", "4u32");
    test_modes!(u32_pow_u32, Pow, "2u32", "2u32", "4u32");

    test_modes!(u64_pow_u8, Pow, "2u64", "2u8", "4u64");
    test_modes!(u64_pow_u16, Pow, "2u64", "2u16", "4u64");
    test_modes!(u64_pow_u32, Pow, "2u64", "2u32", "4u64");

    test_modes!(u128_pow_u8, Pow, "2u128", "2u8", "4u128");
    test_modes!(u128_pow_u16, Pow, "2u128", "2u16", "4u128");
    test_modes!(u128_pow_u32, Pow, "2u128", "2u32", "4u128");

    test_instruction_halts!(
        i8_overflow_halts,
        Pow,
        "Integer overflow on exponentiation of two constants",
        &format!("{}i8.constant", i8::MAX),
        "2u8.constant"
    );
    test_instruction_halts!(
        i16_overflow_halts,
        Pow,
        "Integer overflow on exponentiation of two constants",
        &format!("{}i16.constant", i16::MAX),
        "2u8.constant"
    );
    test_instruction_halts!(
        i32_overflow_halts,
        Pow,
        "Integer overflow on exponentiation of two constants",
        &format!("{}i32.constant", i32::MAX),
        "2u8.constant"
    );
    test_instruction_halts!(
        i64_overflow_halts,
        Pow,
        "Integer overflow on exponentiation of two constants",
        &format!("{}i64.constant", i64::MAX),
        "2u8.constant"
    );
    test_instruction_halts!(
        i128_overflow_halts,
        Pow,
        "Integer overflow on exponentiation of two constants",
        &format!("{}i128.constant", i128::MAX),
        "2u8.constant"
    );
    test_instruction_halts!(
        u8_overflow_halts,
        Pow,
        "Integer overflow on exponentiation of two constants",
        &format!("{}u8.constant", u8::MAX),
        "2u8.constant"
    );
    test_instruction_halts!(
        u16_overflow_halts,
        Pow,
        "Integer overflow on exponentiation of two constants",
        &format!("{}u16.constant", u16::MAX),
        "2u8.constant"
    );
    test_instruction_halts!(
        u32_overflow_halts,
        Pow,
        "Integer overflow on exponentiation of two constants",
        &format!("{}u32.constant", u32::MAX),
        "2u8.constant"
    );
    test_instruction_halts!(
        u64_overflow_halts,
        Pow,
        "Integer overflow on exponentiation of two constants",
        &format!("{}u64.constant", u64::MAX),
        "2u8.constant"
    );
    test_instruction_halts!(
        u128_overflow_halts,
        Pow,
        "Integer overflow on exponentiation of two constants",
        &format!("{}u128.constant", u128::MAX),
        "2u8.constant"
    );

    test_instruction_halts!(
        address_halts,
        Pow,
        "Invalid 'pow' instruction",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.constant",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.constant"
    );
    test_instruction_halts!(boolean_halts, Pow, "Invalid 'pow' instruction", "true.constant", "true.constant");
    test_instruction_halts!(group_halts, Pow, "Invalid 'pow' instruction", "2group.constant", "1u8.constant");
    test_instruction_halts!(scalar_halts, Pow, "Invalid 'pow' instruction", "1scalar.constant", "1u8.constant");
    test_instruction_halts!(string_halts, Pow, "Invalid 'pow' instruction", "\"hello\".constant", "\"world\".constant");

    #[test]
    #[should_panic(expected = "message is not a literal")]
    fn test_composite_halts() {
        let first = Value::<P>::Composite(Identifier::from_str("message"), vec![
            Literal::from_str("2group.public"),
            Literal::from_str("10field.private"),
        ]);
        let second = first.clone();

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.define(&Register::from_str("r2"));
        registers.assign(&Register::from_str("r0"), first);
        registers.assign(&Register::from_str("r1"), second);

        Pow::from_str("r0 r1 into r2").evaluate(&registers);
    }
}
