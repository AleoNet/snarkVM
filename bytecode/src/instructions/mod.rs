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

pub mod add;
pub use add::*;

pub mod store;
pub use store::*;

pub mod sub;
pub use sub::*;

use crate::{Memory, Operation, Sanitizer};
use snarkvm_circuits::ParserResult;
use snarkvm_utilities::{EnumFromBytes, EnumToBytes};

use core::fmt;
use nom::{
    branch::alt,
    bytes::complete::tag,
    combinator::map,
    sequence::{pair, preceded},
};

#[derive(EnumFromBytes, EnumToBytes)]
#[tag(u16)]
pub enum Instruction<M: Memory> {
    /// Adds `first` with `second`, storing the outcome in `destination`.
    Add(Add<M>),
    /// Stores `operand` into `register`, if `destination` is not already set.
    Store(Store<M>),
    /// Subtracts `first` from `second`, storing the outcome in `destination`.
    Sub(Sub<M>),
}

impl<M: Memory> Instruction<M> {
    /// Returns the opcode of the instruction.
    #[inline]
    pub(crate) fn opcode(&self) -> &'static str {
        match self {
            Self::Add(..) => "add",
            Self::Store(..) => "store",
            Self::Sub(..) => "sub",
        }
    }

    /// Evaluates the instruction.
    #[inline]
    pub(crate) fn evaluate(&self, memory: &M) {
        match self {
            Self::Add(instruction) => instruction.evaluate(memory),
            Self::Store(instruction) => instruction.evaluate(memory),
            Self::Sub(instruction) => instruction.evaluate(memory),
        }
    }

    /// Parses a string into an instruction.
    #[inline]
    pub(crate) fn parse(string: &str, memory: M) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the instruction from the string.
        let (string, instruction) = alt((
            // Note that order of the individual parsers matters.
            preceded(pair(tag(Add::<M>::opcode()), tag(" ")), map(|s| Add::parse(s, memory.clone()), Into::into)),
            preceded(pair(tag(Store::<M>::opcode()), tag(" ")), map(|s| Store::parse(s, memory.clone()), Into::into)),
            preceded(pair(tag(Sub::<M>::opcode()), tag(" ")), map(|s| Sub::parse(s, memory.clone()), Into::into)),
        ))(string)?;

        // Parse the semicolon from the string.
        let (string, _) = tag(";")(string)?;

        Ok((string, instruction))
    }
}

impl<M: Memory> fmt::Display for Instruction<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Add(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::Store(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::Sub(instruction) => write!(f, "{} {};", self.opcode(), instruction),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Stack;

    use snarkvm_circuits::Circuit;
    use snarkvm_utilities::{FromBytes, ToBytes};

    #[test]
    fn test_instruction_to_bytes() {
        type M = Stack<Circuit>;
        // Test serialization for the `Add` instruction. Check that the first two bytes are 0u16.
        let instruction = Instruction::<M>::parse("add r0 r2 r1;", M::default()).unwrap().1;
        let bytes = instruction.to_bytes_le().unwrap();
        assert_eq!(u16::from_bytes_le(&bytes[0..2]).unwrap(), 0u16);

        // Test serialization for the `Store` instruction. Check that the first two bytes are 1u16.
        let instruction = Instruction::<M>::parse("store r0 r2;", M::default()).unwrap().1;
        let bytes = instruction.to_bytes_le().unwrap();
        assert_eq!(u16::from_bytes_le(&bytes[0..2]).unwrap(), 1u16);

        // Test serialization for the `Sub` instruction. Check that the first two bytes are 2u16.
        let instruction = Instruction::<M>::parse("sub r0 r2 r1;", M::default()).unwrap().1;
        let bytes = instruction.to_bytes_le().unwrap();
        assert_eq!(u16::from_bytes_le(&bytes[0..2]).unwrap(), 2u16);
    }

    #[test]
    fn test_instruction_to_and_from_bytes() {
        type M = Stack<Circuit>;
        // Test serialization for the `Add` instruction. Check that to_bytes and from_bytes are symmetric in the enum variant.
        let instruction = Instruction::<M>::parse("add r0 r2 r1;", M::default()).unwrap().1;
        let bytes = instruction.to_bytes_le().unwrap();
        let recovered_instruction = Instruction::<M>::from_bytes_le(&bytes).unwrap();
        assert_eq!(std::mem::discriminant(&instruction), std::mem::discriminant(&recovered_instruction));

        // Test serialization for the `Store` instruction. Check that to_bytes and from_bytes are symmetric in the enum variant.
        let instruction = Instruction::<M>::parse("store r0 r2;", M::default()).unwrap().1;
        let bytes = instruction.to_bytes_le().unwrap();
        let recovered_instruction = Instruction::<M>::from_bytes_le(&bytes).unwrap();
        assert_eq!(std::mem::discriminant(&instruction), std::mem::discriminant(&recovered_instruction));

        // Test serialization for the `Sub` instruction. Check that to_bytes and from_bytes are symmetric in the enum variant.
        let instruction = Instruction::<M>::parse("sub r0 r2 r1;", M::default()).unwrap().1;
        let bytes = instruction.to_bytes_le().unwrap();
        let recovered_instruction = Instruction::<M>::from_bytes_le(&bytes).unwrap();
        assert_eq!(std::mem::discriminant(&instruction), std::mem::discriminant(&recovered_instruction));
    }
}
