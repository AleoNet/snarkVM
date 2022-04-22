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
use snarkvm_circuits::{Literal, Parser, ParserResult};
use snarkvm_utilities::{FromBytes, ToBytes};

use core::fmt;
use nom::combinator::map;
use std::io::{Read, Result as IoResult, Write};

/// Flips each bit in the representation of `first`, storing the outcome in `destination`.
pub struct Not<P: Program> {
    operation: UnaryOperation<P>,
}

impl<P: Program> Not<P> {
    /// Returns the operands of the instruction.
    pub fn operands(&self) -> Vec<Operand<P>> {
        self.operation.operands()
    }

    /// Returns the destination register of the instruction.
    pub fn destination(&self) -> &Register<P> {
        self.operation.destination()
    }
}

impl<P: Program> Opcode for Not<P> {
    /// Returns the opcode as a string.
    #[inline]
    fn opcode() -> &'static str {
        "not"
    }
}

impl<P: Program> Operation<P> for Not<P> {
    /// Evaluates the operation.
    #[inline]
    fn evaluate(&self, registers: &Registers<P>) {
        // Load the values for the first and second operands.
        let first = match registers.load(self.operation.first()) {
            Value::Literal(literal) => literal,
            Value::Composite(name, ..) => P::halt(format!("{name} is not a literal")),
        };

        // Perform the operation.
        let result = match first {
            Literal::Boolean(a) => Literal::Boolean(!a),
            Literal::I8(a) => Literal::I8(!a),
            Literal::I16(a) => Literal::I16(!a),
            Literal::I32(a) => Literal::I32(!a),
            Literal::I64(a) => Literal::I64(!a),
            Literal::I128(a) => Literal::I128(!a),
            Literal::U8(a) => Literal::U8(!a),
            Literal::U16(a) => Literal::U16(!a),
            Literal::U32(a) => Literal::U32(!a),
            Literal::U64(a) => Literal::U64(!a),
            Literal::U128(a) => Literal::U128(!a),
            _ => P::halt(format!("Invalid '{}' instruction", Self::opcode())),
        };

        registers.assign(self.operation.destination(), result);
    }
}

impl<P: Program> Parser for Not<P> {
    type Environment = P::Environment;

    /// Parses a string into an 'not' operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the operation from the string.
        map(UnaryOperation::parse, |operation| Self { operation })(string)
    }
}

impl<P: Program> fmt::Display for Not<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.operation)
    }
}

impl<P: Program> FromBytes for Not<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self { operation: UnaryOperation::read_le(&mut reader)? })
    }
}

impl<P: Program> ToBytes for Not<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.operation.write_le(&mut writer)
    }
}

#[allow(clippy::from_over_into)]
impl<P: Program> Into<Instruction<P>> for Not<P> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<P> {
        Instruction::Not(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{test_instruction_halts, test_modes, Identifier, Process};

    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<Process>::parse("not r0 into r1;").unwrap();
        assert!(matches!(instruction, Instruction::Not(_)));
    }

    test_modes!(boolean, Not, "true", "false");
    test_modes!(i8, Not, "0i8", "-1i8");
    test_modes!(i16, Not, "0i16", "-1i16");
    test_modes!(i32, Not, "0i32", "-1i32");
    test_modes!(i64, Not, "0i64", "-1i64");
    test_modes!(i128, Not, "0i128", "-1i128");
    test_modes!(u8, Not, "0u8", &format!("{}u8", u8::MAX));
    test_modes!(u16, Not, "0u16", &format!("{}u16", u16::MAX));
    test_modes!(u32, Not, "0u32", &format!("{}u32", u32::MAX));
    test_modes!(u64, Not, "0u64", &format!("{}u64", u64::MAX));
    test_modes!(u128, Not, "0u128", &format!("{}u128", u128::MAX));

    test_instruction_halts!(
        address_not_halts,
        Not,
        "Invalid 'not' instruction",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.constant"
    );
    test_instruction_halts!(field_not_halts, Not, "Invalid 'not' instruction", "1field.constant");
    test_instruction_halts!(group_not_halts, Not, "Invalid 'not' instruction", "2group.constant");
    test_instruction_halts!(scalar_not_halts, Not, "Invalid 'not' instruction", "1scalar.constant");
    test_instruction_halts!(string_not_halts, Not, "Invalid 'not' instruction", "\"hello\".constant");

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

        Not::from_str("r0 into r1").evaluate(&registers);
    }
}
