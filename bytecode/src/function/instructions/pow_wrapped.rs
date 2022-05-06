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
use snarkvm_circuits::{Literal, Parser, ParserResult, PowWrapped as PowWrappedCircuit};
use snarkvm_utilities::{FromBytes, ToBytes};

use core::fmt;
use nom::combinator::map;
use std::io::{Read, Result as IoResult, Write};

/// Raises `first` to the power of `second`, wrapping around at the boundary of the type, storing the outcome in `destination`.
pub struct PowWrapped<P: Program> {
    operation: BinaryOperation<P>,
}

impl<P: Program> PowWrapped<P> {
    /// Returns the operands of the instruction.
    pub fn operands(&self) -> Vec<Operand<P>> {
        self.operation.operands()
    }

    /// Returns the destination register of the instruction.
    pub fn destination(&self) -> &Register<P> {
        self.operation.destination()
    }
}

impl<P: Program> Opcode for PowWrapped<P> {
    /// Returns the opcode as a string.
    #[inline]
    fn opcode() -> &'static str {
        "pow.w"
    }
}

impl<P: Program> Operation<P> for PowWrapped<P> {
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
            (Literal::I8(a), Literal::U8(b)) => Literal::I8(a.pow_wrapped(&b)),
            (Literal::I8(a), Literal::U16(b)) => Literal::I8(a.pow_wrapped(&b)),
            (Literal::I8(a), Literal::U32(b)) => Literal::I8(a.pow_wrapped(&b)),
            (Literal::I16(a), Literal::U8(b)) => Literal::I16(a.pow_wrapped(&b)),
            (Literal::I16(a), Literal::U16(b)) => Literal::I16(a.pow_wrapped(&b)),
            (Literal::I16(a), Literal::U32(b)) => Literal::I16(a.pow_wrapped(&b)),
            (Literal::I32(a), Literal::U8(b)) => Literal::I32(a.pow_wrapped(&b)),
            (Literal::I32(a), Literal::U16(b)) => Literal::I32(a.pow_wrapped(&b)),
            (Literal::I32(a), Literal::U32(b)) => Literal::I32(a.pow_wrapped(&b)),
            (Literal::I64(a), Literal::U8(b)) => Literal::I64(a.pow_wrapped(&b)),
            (Literal::I64(a), Literal::U16(b)) => Literal::I64(a.pow_wrapped(&b)),
            (Literal::I64(a), Literal::U32(b)) => Literal::I64(a.pow_wrapped(&b)),
            (Literal::I128(a), Literal::U8(b)) => Literal::I128(a.pow_wrapped(&b)),
            (Literal::I128(a), Literal::U16(b)) => Literal::I128(a.pow_wrapped(&b)),
            (Literal::I128(a), Literal::U32(b)) => Literal::I128(a.pow_wrapped(&b)),
            (Literal::U8(a), Literal::U8(b)) => Literal::U8(a.pow_wrapped(&b)),
            (Literal::U8(a), Literal::U16(b)) => Literal::U8(a.pow_wrapped(&b)),
            (Literal::U8(a), Literal::U32(b)) => Literal::U8(a.pow_wrapped(&b)),
            (Literal::U16(a), Literal::U8(b)) => Literal::U16(a.pow_wrapped(&b)),
            (Literal::U16(a), Literal::U16(b)) => Literal::U16(a.pow_wrapped(&b)),
            (Literal::U16(a), Literal::U32(b)) => Literal::U16(a.pow_wrapped(&b)),
            (Literal::U32(a), Literal::U8(b)) => Literal::U32(a.pow_wrapped(&b)),
            (Literal::U32(a), Literal::U16(b)) => Literal::U32(a.pow_wrapped(&b)),
            (Literal::U32(a), Literal::U32(b)) => Literal::U32(a.pow_wrapped(&b)),
            (Literal::U64(a), Literal::U8(b)) => Literal::U64(a.pow_wrapped(&b)),
            (Literal::U64(a), Literal::U16(b)) => Literal::U64(a.pow_wrapped(&b)),
            (Literal::U64(a), Literal::U32(b)) => Literal::U64(a.pow_wrapped(&b)),
            (Literal::U128(a), Literal::U8(b)) => Literal::U128(a.pow_wrapped(&b)),
            (Literal::U128(a), Literal::U16(b)) => Literal::U128(a.pow_wrapped(&b)),
            (Literal::U128(a), Literal::U32(b)) => Literal::U128(a.pow_wrapped(&b)),
            _ => P::halt(format!("Invalid '{}' instruction", Self::opcode())),
        };

        registers.assign(self.operation.destination(), result);
    }
}

impl<P: Program> Parser for PowWrapped<P> {
    type Environment = P::Environment;

    /// Parses a string into a 'pow.w' operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the operation from the string.
        let (string, operation) = map(BinaryOperation::parse, |operation| Self { operation })(string)?;
        // Return the operation.
        Ok((string, operation))
    }
}

impl<P: Program> fmt::Display for PowWrapped<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.operation)
    }
}

impl<P: Program> FromBytes for PowWrapped<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self { operation: BinaryOperation::read_le(&mut reader)? })
    }
}

impl<P: Program> ToBytes for PowWrapped<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.operation.write_le(&mut writer)
    }
}

#[allow(clippy::from_over_into)]
impl<P: Program> Into<Instruction<P>> for PowWrapped<P> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<P> {
        Instruction::PowWrapped(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{test_instruction_halts, test_modes, Identifier, Process, Register};

    type P = Process;

    test_modes!(i8_pow_u8, PowWrapped, "2i8", "7u8", &format!("{}i8", i8::MIN));
    test_modes!(i8_pow_u16, PowWrapped, "2i8", "7u16", &format!("{}i8", i8::MIN));
    test_modes!(i8_pow_u32, PowWrapped, "2i8", "7u32", &format!("{}i8", i8::MIN));

    test_modes!(i16_pow_u8, PowWrapped, "2i16", "15u8", &format!("{}i16", i16::MIN));
    test_modes!(i16_pow_u16, PowWrapped, "2i16", "15u16", &format!("{}i16", i16::MIN));
    test_modes!(i16_pow_u32, PowWrapped, "2i16", "15u32", &format!("{}i16", i16::MIN));

    test_modes!(i32_pow_u8, PowWrapped, "2i32", "31u8", &format!("{}i32", i32::MIN));
    test_modes!(i32_pow_u16, PowWrapped, "2i32", "31u16", &format!("{}i32", i32::MIN));
    test_modes!(i32_pow_u32, PowWrapped, "2i32", "31u32", &format!("{}i32", i32::MIN));

    test_modes!(i64_pow_u8, PowWrapped, "2i64", "63u8", &format!("{}i64", i64::MIN));
    test_modes!(i64_pow_u16, PowWrapped, "2i64", "63u16", &format!("{}i64", i64::MIN));
    test_modes!(i64_pow_u32, PowWrapped, "2i64", "63u32", &format!("{}i64", i64::MIN));

    test_modes!(i128_pow_u8, PowWrapped, "2i128", "127u8", &format!("{}i128", i128::MIN));
    test_modes!(i128_pow_u16, PowWrapped, "2i128", "127u16", &format!("{}i128", i128::MIN));
    test_modes!(i128_pow_u32, PowWrapped, "2i128", "127u32", &format!("{}i128", i128::MIN));

    test_modes!(u8_pow_u8, PowWrapped, "2u8", "8u8", "0u8");
    test_modes!(u8_pow_u16, PowWrapped, "2u8", "8u16", "0u8");
    test_modes!(u8_pow_u32, PowWrapped, "2u8", "8u32", "0u8");

    test_modes!(u16_pow_u8, PowWrapped, "2u16", "16u8", "0u16");
    test_modes!(u16_pow_u16, PowWrapped, "2u16", "16u16", "0u16");
    test_modes!(u16_pow_u32, PowWrapped, "2u16", "16u32", "0u16");

    test_modes!(u32_pow_u8, PowWrapped, "2u32", "32u8", "0u32");
    test_modes!(u32_pow_u16, PowWrapped, "2u32", "32u16", "0u32");
    test_modes!(u32_pow_u32, PowWrapped, "2u32", "32u32", "0u32");

    test_modes!(u64_pow_u8, PowWrapped, "2u64", "64u8", "0u64");
    test_modes!(u64_pow_u16, PowWrapped, "2u64", "64u16", "0u64");
    test_modes!(u64_pow_u32, PowWrapped, "2u64", "64u32", "0u64");

    test_modes!(u128_pow_u8, PowWrapped, "2u128", "128u8", "0u128");
    test_modes!(u128_pow_u16, PowWrapped, "2u128", "128u16", "0u128");
    test_modes!(u128_pow_u32, PowWrapped, "2u128", "128u32", "0u128");

    test_instruction_halts!(
        address_halts,
        PowWrapped,
        "Invalid 'pow.w' instruction",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.constant",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.constant"
    );
    test_instruction_halts!(boolean_halts, PowWrapped, "Invalid 'pow.w' instruction", "true.constant", "true.constant");
    test_instruction_halts!(group_halts, PowWrapped, "Invalid 'pow.w' instruction", "2group.constant", "1u8.constant");
    test_instruction_halts!(
        field_halts,
        PowWrapped,
        "Invalid 'pow.w' instruction",
        "1field.constant",
        "1field.constant"
    );
    test_instruction_halts!(
        scalar_halts,
        PowWrapped,
        "Invalid 'pow.w' instruction",
        "1scalar.constant",
        "1u8.constant"
    );
    test_instruction_halts!(
        string_halts,
        PowWrapped,
        "Invalid 'pow.w' instruction",
        "\"hello\".constant",
        "\"world\".constant"
    );

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

        PowWrapped::from_str("r0 r1 into r2").evaluate(&registers);
    }
}
