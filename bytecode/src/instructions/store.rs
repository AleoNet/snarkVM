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

use crate::{instructions::Instruction, Memory, Operand, Operation, Register, UnaryParser};
use snarkvm_circuits::{Parser, ParserResult};

use core::fmt;

/// Stores `operand` into `register`, if `destination` is not already set.
pub struct Store<M: Memory> {
    destination: Register<M::Environment>,
    operand: Operand<M>,
}

impl<M: Memory> Store<M> {
    /// Initializes a new instance of the 'store' operation.
    pub fn new(destination: Register<M::Environment>, operand: Operand<M>) -> Self {
        Self { destination, operand }
    }
}

impl<M: Memory> Operation for Store<M> {
    type Memory = M;

    const OPCODE: &'static str = "store";

    /// Evaluates the operation in-place.
    fn evaluate(&self) {
        M::store(&self.destination, self.operand.to_value())
    }
}

impl<M: Memory> Parser for Store<M> {
    type Environment = M::Environment;
    type Output = Store<M>;

    /// Parses a string into an 'store' operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self::Output> {
        // Parse the instruction.
        let (string, (destination, operand)) = UnaryParser::parse(Self::OPCODE, string)?;
        // Return the string and instruction.
        Ok((string, Self { destination, operand }))
    }
}

impl<M: Memory> fmt::Display for Store<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", UnaryParser::render(Self::OPCODE, &self.destination, &self.operand))
    }
}

#[allow(clippy::from_over_into)]
impl<M: Memory> Into<Instruction<M>> for Store<M> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<M> {
        Instruction::Store(self)
    }
}
