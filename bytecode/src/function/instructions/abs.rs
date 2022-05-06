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
use snarkvm_circuits::{AbsChecked, Literal, Parser, ParserResult};
use snarkvm_utilities::{FromBytes, ToBytes};

use core::fmt;
use nom::combinator::map;
use std::io::{Read, Result as IoResult, Write};

/// Compute the absolute value of `first`, checking for overflow/underflow, and storing the outcome in `destination`.
pub struct Abs<P: Program> {
    operation: UnaryOperation<P>,
}

impl<P: Program> Abs<P> {
    /// Returns the operands of the instruction.
    pub fn operands(&self) -> Vec<Operand<P>> {
        self.operation.operands()
    }

    /// Returns the destination register of the instruction.
    pub fn destination(&self) -> &Register<P> {
        self.operation.destination()
    }
}

impl<P: Program> Opcode for Abs<P> {
    /// Returns the opcode as a string.
    #[inline]
    fn opcode() -> &'static str {
        "abs"
    }
}

impl<P: Program> Operation<P> for Abs<P> {
    /// Evaluates the operation.
    #[inline]
    fn evaluate(&self, registers: &Registers<P>) {
        // Load the values for the first operand.
        let first = match registers.load(self.operation.first()) {
            Value::Literal(literal) => literal,
            Value::Composite(name, ..) => P::halt(format!("{name} is not a literal")),
        };

        // Perform the operation.
        let result = match first {
            Literal::I8(a) => Literal::I8(a.abs_checked()),
            Literal::I16(a) => Literal::I16(a.abs_checked()),
            Literal::I32(a) => Literal::I32(a.abs_checked()),
            Literal::I64(a) => Literal::I64(a.abs_checked()),
            Literal::I128(a) => Literal::I128(a.abs_checked()),
            Literal::U8(a) => Literal::U8(a.abs_checked()),
            Literal::U16(a) => Literal::U16(a.abs_checked()),
            Literal::U32(a) => Literal::U32(a.abs_checked()),
            Literal::U64(a) => Literal::U64(a.abs_checked()),
            Literal::U128(a) => Literal::U128(a.abs_checked()),
            _ => P::halt(format!("Invalid '{}' instruction", Self::opcode())),
        };

        registers.assign(self.operation.destination(), result);
    }
}

impl<P: Program> Parser for Abs<P> {
    type Environment = P::Environment;

    /// Parses a string into an 'abs' operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the operation from the string.
        map(UnaryOperation::parse, |operation| Self { operation })(string)
    }
}

impl<P: Program> fmt::Display for Abs<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.operation)
    }
}

impl<P: Program> FromBytes for Abs<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self { operation: UnaryOperation::read_le(&mut reader)? })
    }
}

impl<P: Program> ToBytes for Abs<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.operation.write_le(&mut writer)
    }
}

#[allow(clippy::from_over_into)]
impl<P: Program> Into<Instruction<P>> for Abs<P> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<P> {
        Instruction::Abs(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{test_instruction_halts, test_modes, unary_instruction_test, Identifier, Process};

    test_modes!(i8, Abs, "-1i8", "1i8");
    test_modes!(i16, Abs, "-1i16", "1i16");
    test_modes!(i32, Abs, "-1i32", "1i32");
    test_modes!(i64, Abs, "-1i64", "1i64");
    test_modes!(i128, Abs, "-1i128", "1i128");

    // For unsigned integers, Abs and AbsWrapped returns the input value
    unary_instruction_test!(u8, Abs, "1u8.public", "1u8.public");
    unary_instruction_test!(u16, Abs, "1u16.public", "1u16.public");
    unary_instruction_test!(u32, Abs, "1u32.public", "1u32.public");
    unary_instruction_test!(u64, Abs, "1u64.public", "1u64.public");
    unary_instruction_test!(u128, Abs, "1u128.public", "1u128.public");

    test_instruction_halts!(
        i8_min_abs_halts,
        Abs,
        "Integer underflow on subtraction of two constants",
        &format!("{}i8", i8::MIN)
    );
    test_instruction_halts!(
        i16_min_abs_halts,
        Abs,
        "Integer underflow on subtraction of two constants",
        &format!("{}i16", i16::MIN)
    );
    test_instruction_halts!(
        i32_min_abs_halts,
        Abs,
        "Integer underflow on subtraction of two constants",
        &format!("{}i32", i32::MIN)
    );
    test_instruction_halts!(
        i64_min_abs_halts,
        Abs,
        "Integer underflow on subtraction of two constants",
        &format!("{}i64", i64::MIN)
    );
    test_instruction_halts!(
        i128_min_abs_halts,
        Abs,
        "Integer underflow on subtraction of two constants",
        &format!("{}i128", i128::MIN)
    );
    test_instruction_halts!(
        address_abs_halts,
        Abs,
        "Invalid 'abs' instruction",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.constant"
    );
    test_instruction_halts!(boolean_abs_halts, Abs, "Invalid 'abs' instruction", "true.constant");
    test_instruction_halts!(field_abs_halts, Abs, "Invalid 'abs' instruction", "1field.constant");
    test_instruction_halts!(group_abs_halts, Abs, "Invalid 'abs' instruction", "2group.constant");
    test_instruction_halts!(scalar_abs_halts, Abs, "Invalid 'abs' instruction", "1scalar.constant");
    test_instruction_halts!(string_abs_halts, Abs, "Invalid 'abs' instruction", "\"hello\".constant");

    #[test]
    #[should_panic(expected = "message is not a literal")]
    fn test_composite_halts() {
        let first = Value::<Process>::Composite(Identifier::from_str("message"), vec![
            Literal::from_str("2group.public"),
            Literal::from_str("10field.private"),
        ]);

        let registers = Registers::<Process>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.assign(&Register::from_str("r0"), first);

        Abs::from_str("r0 into r1").evaluate(&registers);
    }
}
