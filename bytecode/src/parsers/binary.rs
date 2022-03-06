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

use crate::{Memory, Operand, Register};
use snarkvm_circuits::{Parser, ParserResult};

use core::marker::PhantomData;
use nom::bytes::complete::tag;

pub(crate) struct BinaryParser<M: Memory>(PhantomData<M>);

impl<M: Memory> BinaryParser<M> {
    /// Parses a string into a binary instruction.
    #[inline]
    pub(crate) fn parse<'a>(
        opcode: &'a str,
        string: &'a str,
    ) -> ParserResult<'a, (Register<M::Environment>, Operand<M::Environment>, Operand<M::Environment>)> {
        // Parse the opcode.
        let (string, _) = tag(opcode)(string)?;
        // Parse the space from the string.
        let (string, _) = tag(" ")(string)?;
        // Parse the destination register from the string.
        let (string, destination) = Register::parse(string)?;
        // Parse the space from the string.
        let (string, _) = tag(" ")(string)?;
        // Parse the first operand from the string.
        let (string, first) = Operand::parse(string)?;
        // Parse the space from the string.
        let (string, _) = tag(" ")(string)?;
        // Parse the second operand from the string.
        let (string, second) = Operand::parse(string)?;
        // Parse the semicolon from the string.
        let (string, _) = tag(";")(string)?;

        Ok((string, (destination, first, second)))
    }

    /// Returns a binary instruction as a string.
    #[inline]
    pub(crate) fn render(
        opcode: &str,
        destination: &Register<M::Environment>,
        first: &Operand<M::Environment>,
        second: &Operand<M::Environment>,
    ) -> String {
        format!("{} {} {} {};", opcode, destination, first, second)
    }
}
