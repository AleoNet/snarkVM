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

use crate::{instructions::Instruction, BinaryParser, Immediate, Memory, Operand, Operation, Register};
use snarkvm_circuits::{Parser, ParserResult};

use core::fmt;

/// Subtracts `first` from `second`, storing the outcome in `destination`.
pub struct Sub<M: Memory> {
    destination: Register<M::Environment>,
    first: Operand<M::Environment>,
    second: Operand<M::Environment>,
}

impl<M: Memory> Operation for Sub<M> {
    type Memory = M;

    const OPCODE: &'static str = "sub";

    /// Evaluates the operation in-place.
    fn evaluate(&self) {
        M::initialize(&self.destination);

        // Load the values for the first and second operands, and perform the operation.
        let result = match (self.first.load::<M>(), self.second.load::<M>()) {
            (Immediate::Field(a), Immediate::Field(b)) => (a - b).into(),
            (Immediate::Group(a), Immediate::Group(b)) => (a - b).into(),
            _ => M::halt(format!("Invalid {} instruction", Self::OPCODE)),
        };

        M::store(&self.destination, result);
    }
}

impl<M: Memory> Parser for Sub<M> {
    type Environment = M::Environment;

    /// Parses a string into an 'sub' operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the instruction.
        let (string, (destination, first, second)) = BinaryParser::<M>::parse(Self::OPCODE, string)?;
        // Return the string and instruction.
        Ok((string, Self { destination, first, second }))
    }
}

impl<M: Memory> fmt::Display for Sub<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", BinaryParser::<M>::render(Self::OPCODE, &self.destination, &self.first, &self.second))
    }
}

#[allow(clippy::from_over_into)]
impl<M: Memory> Into<Instruction<M>> for Sub<M> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<M> {
        Instruction::Sub(self)
    }
}
