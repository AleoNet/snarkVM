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

use crate::{instructions::Instruction, BinaryOperation, Immediate, Memory, Operand, Operation, Register};
use snarkvm_circuits::{Parser, ParserResult};

use core::fmt;
use nom::{bytes::complete::tag, combinator::map};

/// Subtracts `first` from `second`, storing the outcome in `destination`.
pub struct Sub<M: Memory> {
    operation: BinaryOperation<M>,
}

impl<M: Memory> Operation for Sub<M> {
    type Memory = M;

    /// Evaluates the operation in-place.
    fn evaluate(&self) {
        // Load the values for the first and second operands, and perform the operation.
        let result = match (self.operation.first(), self.operation.second()) {
            (Immediate::Field(a), Immediate::Field(b)) => (a - b).into(),
            (Immediate::Group(a), Immediate::Group(b)) => (a - b).into(),
            _ => M::halt(format!("Invalid {} instruction", Self::type_name())),
        };

        M::store(&self.operation.destination(), result);
    }
}

impl<M: Memory> Parser for Sub<M> {
    type Environment = M::Environment;

    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "sub"
    }

    /// Parses a string into an 'sub' operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the opcode.
        let (string, _) = tag(Self::type_name())(string)?;
        // Parse the space from the string.
        let (string, _) = tag(" ")(string)?;
        // Parse the operands.
        let (string, operation) = map(BinaryOperation::parse, |operation| Self { operation })(string)?;
        // Parse the semicolon from the string.
        let (string, _) = tag(";")(string)?;

        Ok((string, operation))
    }
}

impl<M: Memory> fmt::Display for Sub<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {};", Self::type_name(), self.operation)
    }
}

#[allow(clippy::from_over_into)]
impl<M: Memory> Into<Instruction<M>> for Sub<M> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<M> {
        Instruction::Sub(self)
    }
}
