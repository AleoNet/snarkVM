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

pub mod argument;
pub use argument::*;

pub mod immediate;
pub use immediate::*;

pub mod operand;
pub use operand::*;

pub mod register;
pub use register::*;

use crate::{instructions::Instruction, Memory};
use snarkvm_circuits::{Environment, ParserResult};

use core::fmt::Display;

// pub trait Operation: Parser + Into<Instruction<Self::Memory>> {
pub trait Operation<E: Environment>: Display {
    ///
    /// Returns the opcode of the instruction.
    ///
    fn opcode() -> &'static str;

    ///
    /// Evaluates the instruction in-place.
    ///
    fn evaluate<M: Memory<Environment = E>>(&self, memory: &M);

    ///
    /// Parses a string literal into an object.
    ///
    fn parse<'a, M: Memory<Environment = E>>(s: &'a str, memory: &'a mut M) -> ParserResult<'a, Self>
    where
        Self: Sized;

    ///
    /// Returns an object from a string literal.
    ///
    fn from_str<M: Memory<Environment = E>>(string: &str, memory: &mut M) -> Self
    where
        Self: Sized,
    {
        match Self::parse(string, memory) {
            Ok((_, circuit)) => circuit,
            Err(error) => M::halt(format!("Failed to parse: {}", error)),
        }
    }
}
