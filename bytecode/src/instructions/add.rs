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

use crate::{instructions::Instruction, BinaryOperation, Immediate, Memory, Operation};
use snarkvm_circuits::ParserResult;

use core::fmt;
use nom::combinator::map;

/// Adds `first` with `second`, storing the outcome in `destination`.
pub struct Add<M: Memory> {
    operation: BinaryOperation<M::Environment>,
}

impl<M: Memory> Operation for Add<M> {
    type Memory = M;

    /// Returns the type name as a string.
    #[inline]
    fn opcode() -> &'static str {
        "add"
    }

    /// Evaluates the operation in-place.
    fn evaluate(&self, memory: &Self::Memory) {
        // Load the values for the first and second operands.
        let first = self.operation.first().load(memory);
        let second = self.operation.second().load(memory);

        // Perform the operation.
        let result = match (first, second) {
            (Immediate::Field(a), Immediate::Field(b)) => (a + b).into(),
            (Immediate::Group(a), Immediate::Group(b)) => (a + b).into(),
            _ => Self::Memory::halt(format!("Invalid '{}' instruction", Self::opcode())),
        };

        memory.store(self.operation.destination(), result);
    }

    /// Parses a string into an 'add' operation.
    #[inline]
    fn parse(string: &str, memory: Self::Memory) -> ParserResult<Self> {
        // Parse the operation from the string.
        let (string, operation) = map(BinaryOperation::parse, |operation| Self { operation })(string)?;
        // Initialize the destination register.
        memory.initialize(operation.operation.destination());
        // Return the operation.
        Ok((string, operation))
    }
}

impl<M: Memory> fmt::Display for Add<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.operation)
    }
}

#[allow(clippy::from_over_into)]
impl<M: Memory> Into<Instruction<M>> for Add<M> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<M> {
        Instruction::Add(self)
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;
//     use crate::Stack;
//
//     #[test]
//     fn test_add() {
//         // let first = Immediate::from_str("1field.public");
//         // let second = Immediate::from_str("1field.private");
//         //
//         // let expected = Immediate::from_str("2field.private");
//
//         Add::<Stack>::from_str("r2 r0 r1");
//
//         //     .evaluate();
//         // let candidate =
//         //
//         // match &candidate[0] {
//         //     Immediate::Field(output) => assert!(output.is_eq(&expected).eject_value()),
//         //     _ => panic!("Failed to load output"),
//         // }
//     }
// }
