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
use snarkvm_circuits::{Literal, MulWrapped as MulWrappedCircuit, Parser, ParserResult};
use snarkvm_utilities::{FromBytes, ToBytes};

use core::fmt;
use nom::combinator::map;
use std::io::{Read, Result as IoResult, Write};

/// Multiplies `first` and `second`, wrapping around at the boundary of the type, storing the outcome in `destination`.
pub struct MulWrapped<P: Program> {
    operation: BinaryOperation<P>,
}

impl<P: Program> MulWrapped<P> {
    /// Returns the operands of the instruction.
    pub fn operands(&self) -> Vec<Operand<P>> {
        self.operation.operands()
    }

    /// Returns the destination register of the instruction.
    pub fn destination(&self) -> &Register<P> {
        self.operation.destination()
    }
}

impl<P: Program> Opcode for MulWrapped<P> {
    /// Returns the opcode as a string.
    #[inline]
    fn opcode() -> &'static str {
        "mul.w"
    }
}

impl<P: Program> Operation<P> for MulWrapped<P> {
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
            (Literal::I8(a), Literal::I8(b)) => Literal::I8(a.mul_wrapped(&b)),
            (Literal::I16(a), Literal::I16(b)) => Literal::I16(a.mul_wrapped(&b)),
            (Literal::I32(a), Literal::I32(b)) => Literal::I32(a.mul_wrapped(&b)),
            (Literal::I64(a), Literal::I64(b)) => Literal::I64(a.mul_wrapped(&b)),
            (Literal::I128(a), Literal::I128(b)) => Literal::I128(a.mul_wrapped(&b)),
            (Literal::U8(a), Literal::U8(b)) => Literal::U8(a.mul_wrapped(&b)),
            (Literal::U16(a), Literal::U16(b)) => Literal::U16(a.mul_wrapped(&b)),
            (Literal::U32(a), Literal::U32(b)) => Literal::U32(a.mul_wrapped(&b)),
            (Literal::U64(a), Literal::U64(b)) => Literal::U64(a.mul_wrapped(&b)),
            (Literal::U128(a), Literal::U128(b)) => Literal::U128(a.mul_wrapped(&b)),
            _ => P::halt(format!("Invalid '{}' instruction", Self::opcode())),
        };

        registers.assign(self.operation.destination(), result);
    }
}

impl<P: Program> Parser for MulWrapped<P> {
    type Environment = P::Environment;

    /// Parses a string into a 'mul.w' operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the operation from the string.
        let (string, operation) = map(BinaryOperation::parse, |operation| Self { operation })(string)?;
        // Return the operation.
        Ok((string, operation))
    }
}

impl<P: Program> fmt::Display for MulWrapped<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.operation)
    }
}

impl<P: Program> FromBytes for MulWrapped<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self { operation: BinaryOperation::read_le(&mut reader)? })
    }
}

impl<P: Program> ToBytes for MulWrapped<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.operation.write_le(&mut writer)
    }
}

#[allow(clippy::from_over_into)]
impl<P: Program> Into<Instruction<P>> for MulWrapped<P> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<P> {
        Instruction::MulWrapped(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{test_instruction_halts, test_modes, Identifier, Process, Register};

    type P = Process;

    // Test that multiplication wraps around at the boundary of the type for all modes.
    test_modes!(i8, MulWrapped, &format!("{}i8", i8::MAX), "2i8", "-2i8");
    test_modes!(i16, MulWrapped, &format!("{}i16", i16::MAX), "2i16", "-2i16");
    test_modes!(i32, MulWrapped, &format!("{}i32", i32::MAX), "2i32", "-2i32");
    test_modes!(i64, MulWrapped, &format!("{}i64", i64::MAX), "2i64", "-2i64");
    test_modes!(i128, MulWrapped, &format!("{}i128", i128::MAX), "2i128", "-2i128");
    test_modes!(u8, MulWrapped, &format!("{}u8", u8::MAX), "2u8", &format!("{}u8", u8::MAX - 1));
    test_modes!(u16, MulWrapped, &format!("{}u16", u16::MAX), "2u16", &format!("{}u16", u16::MAX - 1));
    test_modes!(u32, MulWrapped, &format!("{}u32", u32::MAX), "2u32", &format!("{}u32", u32::MAX - 1));
    test_modes!(u64, MulWrapped, &format!("{}u64", u64::MAX), "2u64", &format!("{}u64", u64::MAX - 1));
    test_modes!(u128, MulWrapped, &format!("{}u128", u128::MAX), "2u128", &format!("{}u128", u128::MAX - 1));

    test_instruction_halts!(
        address_halts,
        MulWrapped,
        "Invalid 'mul.w' instruction",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.constant",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.constant"
    );
    test_instruction_halts!(boolean_halts, MulWrapped, "Invalid 'mul.w' instruction", "true.constant", "true.constant");
    test_instruction_halts!(
        string_halts,
        MulWrapped,
        "Invalid 'mul.w' instruction",
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

        MulWrapped::from_str("r0 r1 into r2").evaluate(&registers);
    }
}
