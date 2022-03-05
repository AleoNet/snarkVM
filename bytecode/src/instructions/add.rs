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

use crate::{instructions::Instruction, Immediate, Memory, Opcode, Operand, Register};
use snarkvm_circuits::{Parser, ParserResult};

use core::fmt;
use nom::bytes::complete::tag;

/// Adds `first` with `second`, storing the outcome in `destination`.
pub struct Add<M: Memory> {
    destination: Register<M::Environment>,
    first: Operand<M>,
    second: Operand<M>,
}

impl<M: Memory> Add<M> {
    /// Initializes a new instance of the 'add' instruction.
    pub fn new(destination: Register<M::Environment>, first: Operand<M>, second: Operand<M>) -> Self {
        Self { destination, first, second }
    }
}

impl<M: Memory> Opcode for Add<M> {
    type Memory = M;

    const NAME: &'static str = "add";

    /// Evaluates the instruction in-place.
    fn evaluate(&self) {
        match (self.first.to_value(), self.second.to_value()) {
            (Immediate::BaseField(a), Immediate::BaseField(b)) => {
                M::store(&self.destination, Immediate::BaseField(a + b))
            }
            (Immediate::Group(a), Immediate::Group(b)) => M::store(&self.destination, Immediate::Group(a + b)),
            _ => M::halt(format!("Invalid {} instruction", Self::NAME)),
        }
    }
}

impl<M: Memory> Parser for Add<M> {
    type Environment = M::Environment;
    type Output = Add<M>;

    /// Parses a string into an 'add' instruction.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self::Output> {
        // Parse the opcode.
        let (string, _) = tag(Self::NAME)(string)?;
        // Parse the destination register from the string.
        let (string, destination) = Register::parse(string)?;
        // Parse the first operand from the string.
        let (string, first) = Operand::parse(string)?;
        // Parse the second operand from the string.
        let (string, second) = Operand::parse(string)?;
        // Parse the semicolon from the string.
        let (string, _) = tag(";")(string)?;

        Ok((string, Self { destination, first, second }))
    }
}

impl<M: Memory> fmt::Display for Add<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {} {} {};", Self::NAME, self.destination, self.first, self.second)
    }
}

#[allow(clippy::from_over_into)]
impl<M: Memory> Into<Instruction<M>> for Add<M> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<M> {
        Instruction::Add(self)
    }
}
