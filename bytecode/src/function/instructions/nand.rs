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
use snarkvm_circuits::{Literal, Nand as NandCircuit, Parser, ParserResult};
use snarkvm_utilities::{FromBytes, ToBytes};

use core::fmt;
use nom::combinator::map;
use std::io::{Read, Result as IoResult, Write};

/// Returns false only if `first` and `second` are true, storing the outcome in `destination`.
pub struct Nand<P: Program> {
    operation: BinaryOperation<P>,
}

impl<P: Program> Nand<P> {
    /// Returns the operands of the instruction.
    pub fn operands(&self) -> Vec<Operand<P>> {
        self.operation.operands()
    }

    /// Returns the destination register of the instruction.
    pub fn destination(&self) -> &Register<P> {
        self.operation.destination()
    }
}

impl<P: Program> Opcode for Nand<P> {
    /// Returns the opcode as a string.
    #[inline]
    fn opcode() -> &'static str {
        "nand"
    }
}

impl<P: Program> Operation<P> for Nand<P> {
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
            (Literal::Boolean(a), Literal::Boolean(b)) => Literal::Boolean(a.nand(&b)),
            _ => P::halt(format!("Invalid '{}' instruction", Self::opcode())),
        };

        registers.assign(self.operation.destination(), result);
    }
}

impl<P: Program> Parser for Nand<P> {
    type Environment = P::Environment;

    /// Parses a string into an 'nand' operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the operation from the string.
        let (string, operation) = map(BinaryOperation::parse, |operation| Self { operation })(string)?;
        // Return the operation.
        Ok((string, operation))
    }
}

impl<P: Program> fmt::Display for Nand<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.operation)
    }
}

impl<P: Program> FromBytes for Nand<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self { operation: BinaryOperation::read_le(&mut reader)? })
    }
}

impl<P: Program> ToBytes for Nand<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.operation.write_le(&mut writer)
    }
}

#[allow(clippy::from_over_into)]
impl<P: Program> Into<Instruction<P>> for Nand<P> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<P> {
        Instruction::Nand(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{binary_instruction_test, test_instruction_halts, test_modes, Identifier, Process};

    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<Process>::parse("nand r0 r1 into r2;").unwrap();
        assert!(matches!(instruction, Instruction::Nand(_)));
    }

    test_modes!(boolean, Nand, "true", "true", "false");
    binary_instruction_test!(boolean_nand_true_and_false, Nand, "true.public", "false.public", "true.private");
    binary_instruction_test!(boolean_nand_false_and_true, Nand, "false.public", "true.public", "true.private");
    binary_instruction_test!(boolean_nand_false_and_false, Nand, "false.public", "false.public", "true.private");

    test_instruction_halts!(
        address_halts,
        Nand,
        "Invalid 'nand' instruction",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.constant",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.constant"
    );
    test_instruction_halts!(i8, Nand, "Invalid 'nand' instruction", "1i8.constant", "0i8.constant");
    test_instruction_halts!(i16, Nand, "Invalid 'nand' instruction", "1i16.constant", "0i16.constant");
    test_instruction_halts!(i32, Nand, "Invalid 'nand' instruction", "1i32.constant", "0i32.constant");
    test_instruction_halts!(i64, Nand, "Invalid 'nand' instruction", "1i64.constant", "0i64.constant");
    test_instruction_halts!(i128, Nand, "Invalid 'nand' instruction", "1i128.constant", "0i128.constant");
    test_instruction_halts!(u8, Nand, "Invalid 'nand' instruction", "1u8.constant", "2u8.constant");
    test_instruction_halts!(u16, Nand, "Invalid 'nand' instruction", "1u16.constant", "2u16.constant");
    test_instruction_halts!(u32, Nand, "Invalid 'nand' instruction", "1u32.constant", "2u32.constant");
    test_instruction_halts!(u64, Nand, "Invalid 'nand' instruction", "1u64.constant", "2u64.constant");
    test_instruction_halts!(u128, Nand, "Invalid 'nand' instruction", "1u128.constant", "2u128.constant");
    test_instruction_halts!(
        string_halts,
        Nand,
        "Invalid 'nand' instruction",
        "\"hello\".constant",
        "\"world\".constant"
    );
    test_instruction_halts!(field_halts, Nand, "Invalid 'nand' instruction", "1field.constant", "1field.constant");
    test_instruction_halts!(group_halts, Nand, "Invalid 'nand' instruction", "2group.constant", "2group.constant");
    test_instruction_halts!(scalar_halts, Nand, "Invalid 'nand' instruction", "1scalar.constant", "1scalar.constant");

    #[test]
    #[should_panic(expected = "message is not a literal")]
    fn test_composite_halts() {
        let first = Value::<Process>::Composite(Identifier::from_str("message"), vec![
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

        Nand::from_str("r0 r1 into r2").evaluate(&registers);
    }
}
