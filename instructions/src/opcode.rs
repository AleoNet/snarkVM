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

use core::num::ParseIntError;
use nom::{
    bytes::complete::tag,
    character::complete::{char, one_of},
    combinator::recognize,
    multi::{many0, many1},
    sequence::terminated,
};

// TODO: Documentation
pub enum Opcode {}

impl Opcode {
    pub fn new(input: &str) -> ParserResult<Opcode> {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
}
