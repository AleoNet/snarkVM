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

use super::*;
use crate::{helpers::Register, Program};
use snarkvm_circuits::prelude::*;
use snarkvm_utilities::{FromBytes, ToBytes};

use core::fmt;
use std::io::{Read, Result as IoResult, Write};

pub(crate) struct BinaryOperation<P: Program> {
    first: Operand<P>,
    second: Operand<P>,
    destination: Register<P>,
}

impl<P: Program> BinaryOperation<P> {
    /// Returns the operands.
    pub fn operands(&self) -> Vec<Operand<P>> {
        vec![self.first.clone(), self.second.clone()]
    }

    /// Returns the first operand.
    pub(crate) fn first(&self) -> &Operand<P> {
        &self.first
    }

    /// Returns the second operand.
    pub(crate) fn second(&self) -> &Operand<P> {
        &self.second
    }

    /// Returns the destination register.
    pub(crate) fn destination(&self) -> &Register<P> {
        &self.destination
    }
}

impl<P: Program> Parser for BinaryOperation<P> {
    type Environment = E;

    /// Parses a string into an operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the first operand from the string.
        let (string, first) = Operand::parse(string)?;
        // Parse the space from the string.
        let (string, _) = tag(" ")(string)?;
        // Parse the second operand from the string.
        let (string, second) = Operand::parse(string)?;
        // Parse the " into " from the string.
        let (string, _) = tag(" into ")(string)?;
        // Parse the destination register from the string.
        let (string, destination) = Register::parse(string)?;

        Ok((string, Self { destination, first, second }))
    }
}

impl<P: Program> fmt::Display for BinaryOperation<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {} into {}", self.first, self.second, self.destination)
    }
}

impl<P: Program> FromBytes for BinaryOperation<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let first = Operand::read_le(&mut reader)?;
        let second = Operand::read_le(&mut reader)?;
        let destination = Register::read_le(&mut reader)?;
        Ok(Self { first, second, destination })
    }
}

impl<P: Program> ToBytes for BinaryOperation<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.first.write_le(&mut writer)?;
        self.second.write_le(&mut writer)?;
        self.destination.write_le(&mut writer)
    }
}
