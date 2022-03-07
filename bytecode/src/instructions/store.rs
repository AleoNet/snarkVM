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

use crate::{instructions::Instruction, Memory, Operation, UnaryOperation};
use snarkvm_circuits::{Environment, Parser, ParserResult};

use core::fmt;
use nom::combinator::map;

/// Stores `operand` into `register`, if `destination` is not already set.
pub struct Store<E: Environment> {
    operation: UnaryOperation<E>,
}

impl<E: Environment> Operation<E> for Store<E> {
    /// Returns the type name as a string.
    #[inline]
    fn opcode() -> &'static str {
        "store"
    }

    /// Evaluates the operation in-place.
    fn evaluate<M: Memory<Environment = E>>(&self, memory: &M) {
        // Load the value for the operand, and store it into the destination register.
        memory.store(self.operation.destination(), self.operation.operand().load(memory))
    }

    /// Parses a string into an 'store' operation.
    #[inline]
    fn parse<'a, M: Memory<Environment = E>>(string: &'a str, memory: &'a mut M) -> ParserResult<'a, Self> {
        // Parse the operation from the string.
        let (string, operation) = map(UnaryOperation::parse, |operation| Self { operation })(string)?;
        // Initialize the destination register.
        memory.initialize(operation.operation.destination());
        // Return the operation.
        Ok((string, operation))
    }
}

impl<E: Environment> fmt::Display for Store<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.operation)
    }
}

#[allow(clippy::from_over_into)]
impl<E: Environment> Into<Instruction<E>> for Store<E> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<E> {
        Instruction::Store(self)
    }
}
