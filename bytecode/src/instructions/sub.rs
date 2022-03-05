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

use crate::{instructions::Instruction, BinaryParser, Immediate, Memory, Opcode, Operand, Register};
use snarkvm_circuits::{Parser, ParserResult};

use core::fmt;

/// Subtracts `first` from `second`, storing the outcome in `destination`.
pub struct Sub<M: Memory> {
    destination: Register<M::Environment>,
    first: Operand<M>,
    second: Operand<M>,
}

impl<M: Memory> Sub<M> {
    /// Initializes a new instance of the 'sub' instruction.
    pub fn new(destination: Register<M::Environment>, first: Operand<M>, second: Operand<M>) -> Self {
        Self { destination, first, second }
    }
}

impl<M: Memory> Opcode for Sub<M> {
    type Memory = M;

    const NAME: &'static str = "sub";

    /// Evaluates the instruction in-place.
    fn evaluate(&self) {
        match (self.first.to_value(), self.second.to_value()) {
            (Immediate::BaseField(a), Immediate::BaseField(b)) => {
                M::store(&self.destination, Immediate::BaseField(a - b))
            }
            (Immediate::Group(a), Immediate::Group(b)) => M::store(&self.destination, Immediate::Group(a - b)),
            _ => M::halt(format!("Invalid {} instruction", Self::NAME)),
        }
    }
}

impl<M: Memory> Parser for Sub<M> {
    type Environment = M::Environment;
    type Output = Sub<M>;

    /// Parses a string into an 'sub' instruction.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self::Output> {
        // Parse the instruction.
        let (string, (destination, first, second)) = BinaryParser::parse(Self::NAME, string)?;
        // Return the string and instruction.
        Ok((string, Self { destination, first, second }))
    }
}

impl<M: Memory> fmt::Display for Sub<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", BinaryParser::render(Self::NAME, &self.destination, &self.first, &self.second))
    }
}

#[allow(clippy::from_over_into)]
impl<M: Memory> Into<Instruction<M>> for Sub<M> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<M> {
        Instruction::Sub(self)
    }
}
