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

use crate::{Immediate, ParserResult, Register};
use snarkvm_circuits::Environment;

use core::num::ParseIntError;
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{char, one_of},
    combinator::{map, recognize},
    multi::{many0, many1},
    sequence::terminated,
    Parser,
};

// TODO: Documentation
pub enum Operand<E: Environment> {
    Immediate(Immediate<E>),
    Register(Register),
}

impl<E: Environment> Operand<E> {
    pub fn new(input: &str) -> ParserResult<Self> {
        alt((map(Immediate::<E>::new, |imm| Self::Immediate(imm)), map(Register::new, |reg| Self::Register(reg))))(
            input,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
}
