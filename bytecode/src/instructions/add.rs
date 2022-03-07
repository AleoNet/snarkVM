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
use snarkvm_circuits::{Parser, ParserResult};

use core::fmt;
use nom::combinator::map;

/// Adds `first` with `second`, storing the outcome in `destination`.
pub struct Add<M: Memory> {
    operation: BinaryOperation<M>,
}

impl<M: Memory> Operation for Add<M> {
    type Memory = M;

    /// Evaluates the operation in-place.
    fn evaluate(&self) {
        // Load the values for the first and second operands, and perform the operation.
        let result = match (self.operation.first(), self.operation.second()) {
            (Immediate::Field(a), Immediate::Field(b)) => (a + b).into(),
            (Immediate::Group(a), Immediate::Group(b)) => (a + b).into(),
            _ => M::halt(format!("Invalid {} instruction", Self::type_name())),
        };

        M::store(&self.operation.destination(), result);
    }
}

impl<M: Memory> Parser for Add<M> {
    type Environment = M::Environment;

    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "add"
    }

    /// Parses a string into an 'add' operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        map(BinaryOperation::parse, |operation| Self { operation })(string)
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
//
// #[cfg(test)]
// mod tests {
//     use super::*;
//
//     #[test]
//     fn test_add() {
//         let first = Immediate::from_str("1field.public");
//         let second = Immediate::from_str("1field.private");
//
//         let expected = Immediate::from_str("2field.private");
//
//         let
//
//         Add::from_str("r2 r0 r1").evaluate();
//         let candidate =
//
//         match &candidate[0] {
//             Immediate::Field(output) => assert!(output.is_eq(&expected).eject_value()),
//             _ => panic!("Failed to load output"),
//         }
//     }
// }
