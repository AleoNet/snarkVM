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

use crate::{Immediate, Memory, Operand, Register};
use snarkvm_circuits::{Parser, ParserResult};

use core::{fmt, marker::PhantomData};
use nom::bytes::complete::tag;

pub(crate) struct UnaryOperation<M: Memory> {
    destination: Register<M::Environment>,
    operand: Operand<M::Environment>,
}

impl<M: Memory> UnaryOperation<M> {
    /// Returns the destination register.
    pub(crate) fn destination(&self) -> &Register<M::Environment> {
        &self.destination
    }

    /// Returns the operand.
    pub(crate) fn operand(&self) -> Immediate<M::Environment> {
        self.operand.load::<M>()
    }
}

impl<M: Memory> Parser for UnaryOperation<M> {
    type Environment = M::Environment;

    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "operation"
    }

    /// Parses a string into an operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the destination register from the string.
        let (string, destination) = Register::parse(string)?;
        // Parse the space from the string.
        let (string, _) = tag(" ")(string)?;
        // Parse the operand from the string.
        let (string, operand) = Operand::parse(string)?;

        // Initialize the destination register.
        M::initialize(&destination);

        Ok((string, Self { destination, operand }))
    }
}

impl<M: Memory> fmt::Display for UnaryOperation<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {}", self.destination, self.operand)
    }
}
