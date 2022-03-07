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

use crate::{Operand, Register};
use snarkvm_circuits::{Environment, Parser, ParserResult};

use core::fmt;
use nom::bytes::complete::tag;

pub(crate) struct UnaryOperation<E: Environment> {
    destination: Register<E>,
    operand: Operand<E>,
}

impl<E: Environment> UnaryOperation<E> {
    /// Returns the destination register.
    pub(crate) fn destination(&self) -> &Register<E> {
        &self.destination
    }

    /// Returns the operand.
    pub(crate) fn operand(&self) -> &Operand<E> {
        &self.operand
    }
}

impl<E: Environment> Parser for UnaryOperation<E> {
    type Environment = E;

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

        Ok((string, Self { destination, operand }))
    }
}

impl<E: Environment> fmt::Display for UnaryOperation<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {}", self.destination, self.operand)
    }
}
