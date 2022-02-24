// Copyright (C) 2019-2021 Aleo Systems Inc.
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

use crate::{Opcode, Operand, ParserResult, Register, Type};
use snarkvm_circuits::Environment;

use core::num::ParseIntError;
use nom::{
    bytes::complete::tag,
    character::complete::{char, one_of},
    combinator::recognize,
    multi::separated_list0,
    sequence::terminated,
};

///
///
pub struct Instruction<E: Environment> {
    op: Opcode,
    sources: Vec<Operand<E>>,
    destinations: Vec<Register>,
}

impl<E: Environment> Instruction<E> {
    pub fn new(input: &str) -> ParserResult<Self> {
        let (input, destinations) = separated_list0(tag(", "), Register::new)(input)?;
        let (input, _) = tag(" := ")(input)?;
        let (input, op) = Opcode::new(input)?;
        let (input, _) = tag(" ")(input)?;
        let (input, sources) = separated_list0(tag(", "), Operand::<E>::new)(input)?;
        let (input, _) = tag(";")(input)?;
        Ok((input, Self { op, sources, destinations }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
}
