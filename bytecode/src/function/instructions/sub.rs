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

/// Subtracts `first` from `second`, storing the outcome in `destination`.
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
            Value::Composite(name, ..) => P::halt(format!("{name} is not a literal")),
        };
        let second = match registers.load(self.operation.second()) {
            Value::Literal(literal) => literal,
            Value::Composite(name, ..) => P::halt(format!("{name} is not a literal")),
        };

        // Perform the operation.
        let result = match (first, second) {
            (Literal::Field(a), Literal::Field(b)) => Literal::Field(a - b),
            (Literal::Group(a), Literal::Group(b)) => Literal::Group(a - b),
            _ => P::halt(format!("Invalid '{}' instruction", Self::opcode())),
        };

        registers.assign(self.operation.destination(), result);
    }
}

impl<P: Program> Parser for Sub<P> {
    type Environment = P::Environment;

    /// Parses a string into an 'sub' operation.
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
    use crate::{Process, Register};

    type P = Process;

    fn check_sub(first: Value<P>, second: Value<P>, expected: Value<P>) {
        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.define(&Register::from_str("r2"));
        registers.assign(&Register::from_str("r0"), first);
        registers.assign(&Register::from_str("r1"), second);

        Sub::from_str("r0 r1 into r2").evaluate(&registers);
        let candidate = registers.load(&Register::from_str("r2"));
        assert_eq!(expected, candidate);
    }

    #[test]
    fn test_sub_field() {
        let first = Value::<P>::from_str("3field.public");
        let second = Value::<P>::from_str("2field.private");
        let expected = Value::<P>::from_str("1field.private");
        check_sub(first, second, expected);
    }

    #[test]
    fn test_sub_group() {
        let first = Value::<P>::from_str("2group.public");
        let second = Value::<P>::from_str("0group.private");
        let expected = Value::<P>::from_str("2group.private");
        check_sub(first, second, expected);
    }
}
