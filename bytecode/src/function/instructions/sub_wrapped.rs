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
use snarkvm_circuits::{Literal, Parser, ParserResult, SubWrapped as SubWrappedCircuit};
use snarkvm_utilities::{FromBytes, ToBytes};

use core::fmt;
use nom::combinator::map;
use std::io::{Read, Result as IoResult, Write};

/// Subtracts `second` from `first`, wrapping around on underflow, and storing the outcome in `destination`.
pub struct SubWrapped<P: Program> {
    operation: BinaryOperation<P>,
}

impl<P: Program> SubWrapped<P> {
    /// Returns the operands of the instruction.
    pub fn operands(&self) -> Vec<Operand<P>> {
        self.operation.operands()
    }

    /// Returns the destination register of the instruction.
    pub fn destination(&self) -> &Register<P> {
        self.operation.destination()
    }
}

impl<P: Program> Opcode for SubWrapped<P> {
    /// Returns the opcode as a string.
    #[inline]
    fn opcode() -> &'static str {
        "sub.w"
    }
}

impl<P: Program> Operation<P> for SubWrapped<P> {
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
            (Literal::I8(a), Literal::I8(b)) => Literal::I8(a.sub_wrapped(&b)),
            (Literal::I16(a), Literal::I16(b)) => Literal::I16(a.sub_wrapped(&b)),
            (Literal::I32(a), Literal::I32(b)) => Literal::I32(a.sub_wrapped(&b)),
            (Literal::I64(a), Literal::I64(b)) => Literal::I64(a.sub_wrapped(&b)),
            (Literal::I128(a), Literal::I128(b)) => Literal::I128(a.sub_wrapped(&b)),
            (Literal::U8(a), Literal::U8(b)) => Literal::U8(a.sub_wrapped(&b)),
            (Literal::U16(a), Literal::U16(b)) => Literal::U16(a.sub_wrapped(&b)),
            (Literal::U32(a), Literal::U32(b)) => Literal::U32(a.sub_wrapped(&b)),
            (Literal::U64(a), Literal::U64(b)) => Literal::U64(a.sub_wrapped(&b)),
            (Literal::U128(a), Literal::U128(b)) => Literal::U128(a.sub_wrapped(&b)),
            _ => P::halt(format!("Invalid '{}' instruction", Self::opcode())),
        };

        registers.assign(self.operation.destination(), result);
    }
}

impl<P: Program> Parser for SubWrapped<P> {
    type Environment = P::Environment;

    /// Parses a string into an 'SubWrapped' operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the operation from the string.
        map(BinaryOperation::parse, |operation| Self { operation })(string)
    }
}

impl<P: Program> fmt::Display for SubWrapped<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.operation)
    }
}

impl<P: Program> FromBytes for SubWrapped<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self { operation: BinaryOperation::read_le(&mut reader)? })
    }
}

impl<P: Program> ToBytes for SubWrapped<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.operation.write_le(&mut writer)
    }
}

#[allow(clippy::from_over_into)]
impl<P: Program> Into<Instruction<P>> for SubWrapped<P> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<P> {
        Instruction::SubWrapped(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{test_instruction_halts, test_modes, Identifier, Process, Register};

    type P = Process;

    // Tests that the SubWrapped instruction will wrap around on underflow in every mode.
    test_modes!(i8, SubWrapped, &format!("{}i8", i8::MIN), "1i8", &format!("{}i8", i8::MAX));
    test_modes!(i16, SubWrapped, &format!("{}i16", i16::MIN), "1i16", &format!("{}i16", i16::MAX));
    test_modes!(i32, SubWrapped, &format!("{}i32", i32::MIN), "1i32", &format!("{}i32", i32::MAX));
    test_modes!(i64, SubWrapped, &format!("{}i64", i64::MIN), "1i64", &format!("{}i64", i64::MAX));
    test_modes!(i128, SubWrapped, &format!("{}i128", i128::MIN), "1i128", &format!("{}i128", i128::MAX));
    test_modes!(u8, SubWrapped, &format!("{}u8", u8::MIN), "1u8", &format!("{}u8", u8::MAX));
    test_modes!(u16, SubWrapped, &format!("{}u16", u16::MIN), "1u16", &format!("{}u16", u16::MAX));
    test_modes!(u32, SubWrapped, &format!("{}u32", u32::MIN), "1u32", &format!("{}u32", u32::MAX));
    test_modes!(u64, SubWrapped, &format!("{}u64", u64::MIN), "1u64", &format!("{}u64", u64::MAX));
    test_modes!(u128, SubWrapped, &format!("{}u128", u128::MIN), "1u128", &format!("{}u128", u128::MAX));

    test_instruction_halts!(
        address_halts,
        SubWrapped,
        "Invalid 'sub.w' instruction",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.constant",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.constant"
    );
    test_instruction_halts!(boolean_halts, SubWrapped, "Invalid 'sub.w' instruction", "true.constant", "true.constant");
    test_instruction_halts!(
        string_halts,
        SubWrapped,
        "Invalid 'sub.w' instruction",
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

        SubWrapped::from_str("r0 r1 into r2").evaluate(&registers);
    }
}
