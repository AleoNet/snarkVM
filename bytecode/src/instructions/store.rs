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

use crate::{instructions::Instruction, Memory, Operand, Operation, Register, UnaryOperation};
use snarkvm_circuits::{Parser, ParserResult};

use core::fmt;
use nom::{bytes::complete::tag, combinator::map};

/// Stores `operand` into `register`, if `destination` is not already set.
pub struct Store<M: Memory> {
    operation: UnaryOperation<M>,
}

impl<M: Memory> Operation for Store<M> {
    type Memory = M;

    /// Evaluates the operation in-place.
    fn evaluate(&self) {
        // Load the value for the operand, and store it into the destination register.
        M::store(&self.operation.destination(), self.operation.operand())
    }
}

impl<M: Memory> Parser for Store<M> {
    type Environment = M::Environment;

    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "store"
    }

    /// Parses a string into an 'store' operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the opcode.
        let (string, _) = tag(Self::type_name())(string)?;
        // Parse the space from the string.
        let (string, _) = tag(" ")(string)?;
        // Parse the operands.
        let (string, operation) = map(UnaryOperation::parse, |operation| Self { operation })(string)?;
        // Parse the semicolon from the string.
        let (string, _) = tag(";")(string)?;

        Ok((string, operation))
    }
}

impl<M: Memory> fmt::Display for Store<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {};", Self::type_name(), self.operation)
    }
}

#[allow(clippy::from_over_into)]
impl<M: Memory> Into<Instruction<M>> for Store<M> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<M> {
        Instruction::Store(self)
    }
}
