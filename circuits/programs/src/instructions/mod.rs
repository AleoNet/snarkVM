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

mod add;
mod store;
mod sub;

use crate::{Immediate, Memory, Operand, Register};
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
    /// Adds `first` with `second`, storing the outcome in `register`.
    Add(Register<M::Environment>, Operand<M>, Operand<M>),
    /// Stores `operand` into `register`, if `register` is not already set.
    Store(Register<M::Environment>, Operand<M>),
    /// Subtracts `first` from `second`, storing the outcome in `register`.
    Sub(Register<M::Environment>, Operand<M>, Operand<M>),
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
            Self::Add(register, first, second) => Self::add(register, first, second),
            Self::Store(register, operand) => Self::store(register, operand),
            Self::Sub(register, first, second) => Self::sub(register, first, second),
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
//         alt((
//             map(|string: &str| -> ParserResult<Self::Output> {
//                 // Parse the 'let ' from the string.
//                 let (string, _) = tag("let ")(string)?;
//                 // Parse the register from the string.
//                 let (string, register) = Register::parse(string)?;
//                 // Parse the ' = ' from the string.
//                 let (string, _) = tag(" = ")(string)?;
//                 // Parse the first operand from the string.
//                 let (string, first) = Operand::parse(string)?;
//                 // Parse the ' + ' from the string.
//                 let (string, _) = tag(" + ")(string)?;
//                 // Parse the second operand from the string.
//                 let (string, second) = Operand::parse(string)?;
//                 // Parse the semicolon from the string.
//                 let (string, _) = tag(";")(string)?;
//
//                 Ok((string, Self::Add(register, first, second)))
//             }, |instruction| instruction),
//         ))(string)
//     }
// }

impl<M: Memory> fmt::Display for Instruction<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Add(register, first, second) => write!(f, "let {} = {} + {};", register, first, second),
            Self::Store(register, operand) => write!(f, "let {} = {};", register, operand),
            Self::Sub(register, first, second) => write!(f, "let {} = {} - {};", register, first, second),
        }
    }
}
