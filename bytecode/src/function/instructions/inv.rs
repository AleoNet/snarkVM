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
use snarkvm_circuits::{Inv as InvCircuit, Literal, Parser, ParserResult};
use snarkvm_utilities::{FromBytes, ToBytes};

use core::fmt;
use nom::combinator::map;
use std::io::{Read, Result as IoResult, Write};

/// Computes the multiplicative inverse of `first`, storing the outcome in `destination`.
pub struct Inv<P: Program> {
    operation: UnaryOperation<P>,
}

impl<P: Program> Inv<P> {
    /// Returns the operands of the instruction.
    pub fn operands(&self) -> Vec<Operand<P>> {
        self.operation.operands()
    }

    /// Returns the destination register of the instruction.
    pub fn destination(&self) -> &Register<P> {
        self.operation.destination()
    }
}

impl<P: Program> Opcode for Inv<P> {
    /// Returns the opcode as a string.
    #[inline]
    fn opcode() -> &'static str {
        "inv"
    }
}

impl<P: Program> Operation<P> for Inv<P> {
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
            Literal::Field(a) => Literal::Field(a.inv()),
            _ => P::halt(format!("Invalid '{}' instruction", Self::opcode())),
        };

        registers.assign(self.operation.destination(), result);
    }
}

impl<P: Program> Parser for Inv<P> {
    type Environment = P::Environment;

    /// Parses a string into an 'inv' operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the operation from the string.
        map(UnaryOperation::parse, |operation| Self { operation })(string)
    }
}

impl<P: Program> fmt::Display for Inv<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.operation)
    }
}

impl<P: Program> FromBytes for Inv<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self { operation: UnaryOperation::read_le(&mut reader)? })
    }
}

impl<P: Program> ToBytes for Inv<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.operation.write_le(&mut writer)
    }
}

#[allow(clippy::from_over_into)]
impl<P: Program> Into<Instruction<P>> for Inv<P> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<P> {
        Instruction::Inv(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{test_instruction_halts, test_modes, unary_instruction_test, Identifier, Process};

    test_modes!(field, Inv, "1field", "1field");
    unary_instruction_test!(
        field_inv,
        Inv,
        "2field.public",
        "4222230874714185212124412469390773265687949667577031913967616727958704619521field.private"
    );

    test_instruction_halts!(
        field_zero_inv_halts,
        Inv,
        "Failed to compute the inverse for a base field element",
        "0field.constant"
    );
    test_instruction_halts!(i8_inv_halts, Inv, "Invalid 'inv' instruction", "1i8.constant");
    test_instruction_halts!(i16_inv_halts, Inv, "Invalid 'inv' instruction", "1i16.constant");
    test_instruction_halts!(i32_inv_halts, Inv, "Invalid 'inv' instruction", "1i32.constant");
    test_instruction_halts!(i64_inv_halts, Inv, "Invalid 'inv' instruction", "1i64.constant");
    test_instruction_halts!(i128_inv_halts, Inv, "Invalid 'inv' instruction", "1i128.constant");
    test_instruction_halts!(u8_inv_halts, Inv, "Invalid 'inv' instruction", "1u8.constant");
    test_instruction_halts!(u16_inv_halts, Inv, "Invalid 'inv' instruction", "1u16.constant");
    test_instruction_halts!(u32_inv_halts, Inv, "Invalid 'inv' instruction", "1u32.constant");
    test_instruction_halts!(u64_inv_halts, Inv, "Invalid 'inv' instruction", "1u64.constant");
    test_instruction_halts!(u128_inv_halts, Inv, "Invalid 'inv' instruction", "1u128.constant");
    test_instruction_halts!(scalar_inv_halts, Inv, "Invalid 'inv' instruction", "1scalar.constant");
    test_instruction_halts!(group_inv_halts, Inv, "Invalid 'inv' instruction", "2group.constant");
    test_instruction_halts!(
        address_inv_halts,
        Inv,
        "Invalid 'inv' instruction",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.constant"
    );
    test_instruction_halts!(boolean_inv_halts, Inv, "Invalid 'inv' instruction", "true.constant");
    test_instruction_halts!(string_inv_halts, Inv, "Invalid 'inv' instruction", "\"hello\".constant");

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

        Inv::from_str("r0 into r1").evaluate(&registers);
    }
}
