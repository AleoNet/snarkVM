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
use snarkvm_circuits::{Literal, Parser, ParserResult, ShlChecked};
use snarkvm_utilities::{FromBytes, ToBytes};

use core::fmt;
use nom::combinator::map;
use std::io::{Read, Result as IoResult, Write};

/// Shifts `first` left by `second` bits, storing the outcome in `destination`.
pub struct Shl<P: Program> {
    operation: BinaryOperation<P>,
}

impl<P: Program> Shl<P> {
    /// Returns the operands of the instruction.
    pub fn operands(&self) -> Vec<Operand<P>> {
        self.operation.operands()
    }

    /// Returns the destination register of the instruction.
    pub fn destination(&self) -> &Register<P> {
        self.operation.destination()
    }
}

impl<P: Program> Opcode for Shl<P> {
    /// Returns the opcode as a string.
    #[inline]
    fn opcode() -> &'static str {
        "shl"
    }
}

impl<P: Program> Operation<P> for Shl<P> {
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
            (Literal::I8(a), Literal::U8(b)) => Literal::I8(a.shl_checked(&b)),
            (Literal::I8(a), Literal::U16(b)) => Literal::I8(a.shl_checked(&b)),
            (Literal::I8(a), Literal::U32(b)) => Literal::I8(a.shl_checked(&b)),
            (Literal::I16(a), Literal::U8(b)) => Literal::I16(a.shl_checked(&b)),
            (Literal::I16(a), Literal::U16(b)) => Literal::I16(a.shl_checked(&b)),
            (Literal::I16(a), Literal::U32(b)) => Literal::I16(a.shl_checked(&b)),
            (Literal::I32(a), Literal::U8(b)) => Literal::I32(a.shl_checked(&b)),
            (Literal::I32(a), Literal::U16(b)) => Literal::I32(a.shl_checked(&b)),
            (Literal::I32(a), Literal::U32(b)) => Literal::I32(a.shl_checked(&b)),
            (Literal::I64(a), Literal::U8(b)) => Literal::I64(a.shl_checked(&b)),
            (Literal::I64(a), Literal::U16(b)) => Literal::I64(a.shl_checked(&b)),
            (Literal::I64(a), Literal::U32(b)) => Literal::I64(a.shl_checked(&b)),
            (Literal::I128(a), Literal::U8(b)) => Literal::I128(a.shl_checked(&b)),
            (Literal::I128(a), Literal::U16(b)) => Literal::I128(a.shl_checked(&b)),
            (Literal::I128(a), Literal::U32(b)) => Literal::I128(a.shl_checked(&b)),
            (Literal::U8(a), Literal::U8(b)) => Literal::U8(a.shl_checked(&b)),
            (Literal::U8(a), Literal::U16(b)) => Literal::U8(a.shl_checked(&b)),
            (Literal::U8(a), Literal::U32(b)) => Literal::U8(a.shl_checked(&b)),
            (Literal::U16(a), Literal::U8(b)) => Literal::U16(a.shl_checked(&b)),
            (Literal::U16(a), Literal::U16(b)) => Literal::U16(a.shl_checked(&b)),
            (Literal::U16(a), Literal::U32(b)) => Literal::U16(a.shl_checked(&b)),
            (Literal::U32(a), Literal::U8(b)) => Literal::U32(a.shl_checked(&b)),
            (Literal::U32(a), Literal::U16(b)) => Literal::U32(a.shl_checked(&b)),
            (Literal::U32(a), Literal::U32(b)) => Literal::U32(a.shl_checked(&b)),
            (Literal::U64(a), Literal::U8(b)) => Literal::U64(a.shl_checked(&b)),
            (Literal::U64(a), Literal::U16(b)) => Literal::U64(a.shl_checked(&b)),
            (Literal::U64(a), Literal::U32(b)) => Literal::U64(a.shl_checked(&b)),
            (Literal::U128(a), Literal::U8(b)) => Literal::U128(a.shl_checked(&b)),
            (Literal::U128(a), Literal::U16(b)) => Literal::U128(a.shl_checked(&b)),
            (Literal::U128(a), Literal::U32(b)) => Literal::U128(a.shl_checked(&b)),
            _ => P::halt(format!("Invalid '{}' instruction", Self::opcode())),
        };

        registers.assign(self.operation.destination(), result);
    }
}

impl<P: Program> Parser for Shl<P> {
    type Environment = P::Environment;

    /// Parses a string into a 'shl' operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the operation from the string.
        let (string, operation) = map(BinaryOperation::parse, |operation| Self { operation })(string)?;
        // Return the operation.
        Ok((string, operation))
    }
}

impl<P: Program> fmt::Display for Shl<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.operation)
    }
}

impl<P: Program> FromBytes for Shl<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self { operation: BinaryOperation::read_le(&mut reader)? })
    }
}

impl<P: Program> ToBytes for Shl<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.operation.write_le(&mut writer)
    }
}

#[allow(clippy::from_over_into)]
impl<P: Program> Into<Instruction<P>> for Shl<P> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<P> {
        Instruction::Shl(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{test_instruction_halts, test_modes, Identifier, Process, Register};

    type P = Process;

    const SHL_MODES: [[&str; 3]; 9] = [
        ["public", "public", "private"],
        ["public", "constant", "public"],
        ["public", "private", "private"],
        ["private", "constant", "private"],
        ["private", "public", "private"],
        ["private", "private", "private"],
        ["constant", "private", "private"],
        ["constant", "public", "private"],
        ["constant", "constant", "constant"],
    ];

    test_modes!(i8_shl_u8, Shl, "1i8", "7u8", &format!("{}i8", 1i8 << 7), SHL_MODES);
    test_modes!(i8_shl_u16, Shl, "1i8", "7u16", &format!("{}i8", 1i8 << 7), SHL_MODES);
    test_modes!(i8_shl_u32, Shl, "1i8", "7u32", &format!("{}i8", 1i8 << 7), SHL_MODES);

    test_modes!(i16_shl_u8, Shl, "1i16", "15u8", &format!("{}i16", 1i16 << 15), SHL_MODES);
    test_modes!(i16_shl_u16, Shl, "1i16", "15u16", &format!("{}i16", 1i16 << 15), SHL_MODES);
    test_modes!(i16_shl_u32, Shl, "1i16", "15u32", &format!("{}i16", 1i16 << 15), SHL_MODES);

    test_modes!(i32_shl_u8, Shl, "1i32", "31u8", &format!("{}i32", 1i32 << 31), SHL_MODES);
    test_modes!(i32_shl_u16, Shl, "1i32", "31u16", &format!("{}i32", 1i32 << 31), SHL_MODES);
    test_modes!(i32_shl_u32, Shl, "1i32", "31u32", &format!("{}i32", 1i32 << 31), SHL_MODES);

    test_modes!(i64_shl_u8, Shl, "1i64", "63u8", &format!("{}i64", 1i64 << 63), SHL_MODES);
    test_modes!(i64_shl_u16, Shl, "1i64", "63u16", &format!("{}i64", 1i64 << 63), SHL_MODES);
    test_modes!(i64_shl_u32, Shl, "1i64", "63u32", &format!("{}i64", 1i64 << 63), SHL_MODES);

    test_modes!(i128_shl_u8, Shl, "1i128", "127u8", &format!("{}i128", 1i128 << 127), SHL_MODES);
    test_modes!(i128_shl_u16, Shl, "1i128", "127u16", &format!("{}i128", 1i128 << 127), SHL_MODES);
    test_modes!(i128_shl_u32, Shl, "1i128", "127u32", &format!("{}i128", 1i128 << 127), SHL_MODES);

    test_modes!(u8_shl_u8, Shl, "1u8", "7u8", &format!("{}u8", 1u8 << 7), SHL_MODES);
    test_modes!(u8_shl_u16, Shl, "1u8", "7u16", &format!("{}u8", 1u8 << 7), SHL_MODES);
    test_modes!(u8_shl_u32, Shl, "1u8", "7u32", &format!("{}u8", 1u8 << 7), SHL_MODES);

    test_modes!(u16_shl_u8, Shl, "1u16", "15u8", &format!("{}u16", 1u16 << 15), SHL_MODES);
    test_modes!(u16_shl_u16, Shl, "1u16", "15u16", &format!("{}u16", 1u16 << 15), SHL_MODES);
    test_modes!(u16_shl_u32, Shl, "1u16", "15u32", &format!("{}u16", 1u16 << 15), SHL_MODES);

    test_modes!(u32_shl_u8, Shl, "1u32", "31u8", &format!("{}u32", 1u32 << 31), SHL_MODES);
    test_modes!(u32_shl_u16, Shl, "1u32", "31u16", &format!("{}u32", 1u32 << 31), SHL_MODES);
    test_modes!(u32_shl_u32, Shl, "1u32", "31u32", &format!("{}u32", 1u32 << 31), SHL_MODES);

    test_modes!(u64_shl_u8, Shl, "1u64", "63u8", &format!("{}u64", 1u64 << 63), SHL_MODES);
    test_modes!(u64_shl_u16, Shl, "1u64", "63u16", &format!("{}u64", 1u64 << 63), SHL_MODES);
    test_modes!(u64_shl_u32, Shl, "1u64", "63u32", &format!("{}u64", 1u64 << 63), SHL_MODES);

    test_modes!(u128_shl_u8, Shl, "1u128", "127u8", &format!("{}u128", 1u128 << 127), SHL_MODES);
    test_modes!(u128_shl_u16, Shl, "1u128", "127u16", &format!("{}u128", 1u128 << 127), SHL_MODES);
    test_modes!(u128_shl_u32, Shl, "1u128", "127u32", &format!("{}u128", 1u128 << 127), SHL_MODES);

    test_instruction_halts!(
        i8_shl_constant_exceeds_bitwidth_halts,
        Shl,
        "Constant shifted by constant exceeds the allowed bitwidth.",
        "2i8.constant",
        "8u8.constant"
    );
    test_instruction_halts!(
        i8_shl_exceeds_bitwidth_halts,
        Shl,
        "Integer shifted by constant exceeds the allowed bitwidth.",
        "2i8.public",
        "8u8.constant"
    );
    test_instruction_halts!(
        i16_shl_constant_exceeds_bitwidth_halts,
        Shl,
        "Constant shifted by constant exceeds the allowed bitwidth.",
        "2i16.constant",
        "16u8.constant"
    );
    test_instruction_halts!(
        i16_shl_exceeds_bitwidth_halts,
        Shl,
        "Integer shifted by constant exceeds the allowed bitwidth.",
        "2i16.public",
        "16u8.constant"
    );
    test_instruction_halts!(
        i32_shl_constant_exceeds_bitwidth_halts,
        Shl,
        "Constant shifted by constant exceeds the allowed bitwidth.",
        "2i32.constant",
        "32u8.constant"
    );
    test_instruction_halts!(
        i32_shl_exceeds_bitwidth_halts,
        Shl,
        "Integer shifted by constant exceeds the allowed bitwidth.",
        "2i32.public",
        "32u8.constant"
    );
    test_instruction_halts!(
        i64_shl_constant_exceeds_bitwidth_halts,
        Shl,
        "Constant shifted by constant exceeds the allowed bitwidth.",
        "2i64.constant",
        "64u8.constant"
    );
    test_instruction_halts!(
        i64_shl_exceeds_bitwidth_halts,
        Shl,
        "Integer shifted by constant exceeds the allowed bitwidth.",
        "2i64.public",
        "64u8.constant"
    );
    test_instruction_halts!(
        i128_shl_constant_exceeds_bitwidth_halts,
        Shl,
        "Constant shifted by constant exceeds the allowed bitwidth.",
        "2i128.constant",
        "128u16.constant"
    );
    test_instruction_halts!(
        i128_shl_exceeds_bitwidth_halts,
        Shl,
        "Integer shifted by constant exceeds the allowed bitwidth.",
        "2i128.public",
        "128u16.constant"
    );
    test_instruction_halts!(
        u8_shl_constant_exceeds_bitwidth_halts,
        Shl,
        "Constant shifted by constant exceeds the allowed bitwidth.",
        "2u8.constant",
        "8u8.constant"
    );
    test_instruction_halts!(
        u8_shl_exceeds_bitwidth_halts,
        Shl,
        "Integer shifted by constant exceeds the allowed bitwidth.",
        "2u8.public",
        "8u8.constant"
    );
    test_instruction_halts!(
        u16_shl_constant_exceeds_bitwidth_halts,
        Shl,
        "Constant shifted by constant exceeds the allowed bitwidth.",
        "2u16.constant",
        "16u8.constant"
    );
    test_instruction_halts!(
        u16_shl_exceeds_bitwidth_halts,
        Shl,
        "Integer shifted by constant exceeds the allowed bitwidth.",
        "2u16.public",
        "16u8.constant"
    );
    test_instruction_halts!(
        u32_shl_constant_exceeds_bitwidth_halts,
        Shl,
        "Constant shifted by constant exceeds the allowed bitwidth.",
        "2u32.constant",
        "32u8.constant"
    );
    test_instruction_halts!(
        u32_shl_exceeds_bitwidth_halts,
        Shl,
        "Integer shifted by constant exceeds the allowed bitwidth.",
        "2u32.public",
        "32u8.constant"
    );
    test_instruction_halts!(
        u64_shl_constant_exceeds_bitwidth_halts,
        Shl,
        "Constant shifted by constant exceeds the allowed bitwidth.",
        "2u64.constant",
        "64u8.constant"
    );
    test_instruction_halts!(
        u64_shl_exceeds_bitwidth_halts,
        Shl,
        "Integer shifted by constant exceeds the allowed bitwidth.",
        "2u64.public",
        "64u8.constant"
    );
    test_instruction_halts!(
        u128_shl_constant_exceeds_bitwidth_halts,
        Shl,
        "Constant shifted by constant exceeds the allowed bitwidth.",
        "2u128.constant",
        "128u16.constant"
    );
    test_instruction_halts!(
        u128_shl_exceeds_bitwidth_halts,
        Shl,
        "Integer shifted by constant exceeds the allowed bitwidth.",
        "2u128.public",
        "128u16.constant"
    );

    test_instruction_halts!(
        address_halts,
        Shl,
        "Invalid 'shl' instruction",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.constant",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.constant"
    );
    test_instruction_halts!(boolean_halts, Shl, "Invalid 'shl' instruction", "true.constant", "true.constant");
    test_instruction_halts!(group_halts, Shl, "Invalid 'shl' instruction", "2group.constant", "1u8.constant");
    test_instruction_halts!(field_halts, Shl, "Invalid 'shl' instruction", "1field.constant", "1u8.constant");
    test_instruction_halts!(scalar_halts, Shl, "Invalid 'shl' instruction", "1scalar.constant", "1u8.constant");
    test_instruction_halts!(string_halts, Shl, "Invalid 'shl' instruction", "\"hello\".constant", "\"world\".constant");

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

        Shl::from_str("r0 r1 into r2").evaluate(&registers);
    }
}
