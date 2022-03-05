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

use crate::{Immediate, Memory, Opcode, Operand, Register};
use snarkvm_circuits::{Parser, ParserResult};

use core::fmt;
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::one_of,
    combinator::{map, map_res, recognize},
    multi::many1,
};

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
    pub fn opcode(&self) -> u16 {
        match self {
            Self::Add(..) => 0,
            Self::Store(..) => 1,
            Self::Sub(..) => 2,
        }
    }

    /// Evaluates the instruction.
    pub fn evaluate(&self) {
        match self {
            Self::Add(instruction) => instruction.evaluate(),
            Self::Store(instruction) => instruction.evaluate(),
            Self::Sub(instruction) => instruction.evaluate(),
        }
    }
}

// impl<M: Memory> Parser for Instruction<M> {
//     type Environment = M::Environment;
//     type Output = Instruction<M>;
//
//     /// Parses a string into an instruction.
//     #[inline]
//     fn parse(string: &str) -> ParserResult<Self::Output> {
//         let (string, ) = alt((
//             // Note that order of the individual parsers matters.
//             map(tag("add"), |_| Opcode::Add),
//             map(tag("store"), |_| Opcode::Store),
//             map(tag("sub"), |_| Opcode::Sub),
//         ))(string)?;
//
//         // alt((
//         //     map(|string: &str| -> ParserResult<Self::Output> {
//         //         // Parse the 'let ' from the string.
//         //         let (string, _) = tag("let ")(string)?;
//         //         // Parse the register from the string.
//         //         let (string, register) = Register::parse(string)?;
//         //         // Parse the ' = ' from the string.
//         //         let (string, _) = tag(" = ")(string)?;
//         //         // Parse the first operand from the string.
//         //         let (string, first) = Operand::parse(string)?;
//         //         // Parse the ' + ' from the string.
//         //         let (string, _) = tag(" + ")(string)?;
//         //         // Parse the second operand from the string.
//         //         let (string, second) = Operand::parse(string)?;
//         //         // Parse the semicolon from the string.
//         //         let (string, _) = tag(";")(string)?;
//         //
//         //         Ok((string, Self::Add(register, first, second)))
//         //     }, |instruction| instruction),
//         // ))(string)
//     }
// }
//
// impl<M: Memory> fmt::Display for Instruction<M> {
//     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//         match self {
//             Self::Add(instruction) => instruction.fmt(f),
//             Self::Store(instruction) => instruction.fmt(f),
//             Self::Sub(instruction) => instruction.fmt(f),
//         }
//     }
// }
