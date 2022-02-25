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

use crate::{Immediate, ParserResult, Register, Type};

use core::num::ParseIntError;
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{char, one_of},
    combinator::{map, recognize},
    multi::{many0, many1},
    sequence::terminated,
};

// TODO: Documentation
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Opcode {
    Add,
    AddChecked,
    AddWrapped,
    And,
    Eq,
    Sub,
    SubChecked,
    SubWrapped,
    Ternary,
}

impl Opcode {
    pub fn new(input: &str) -> ParserResult<Opcode> {
        alt((
            // Note that order of the individual parsers matters.
            map(tag("addc"), |_| Opcode::AddChecked),
            map(tag("addw"), |_| Opcode::AddWrapped),
            map(tag("add"), |_| Opcode::Add),
            map(tag("and"), |_| Opcode::And),
            map(tag("eq"), |_| Opcode::Eq),
            map(tag("subc"), |_| Opcode::SubChecked),
            map(tag("subw"), |_| Opcode::SubWrapped),
            map(tag("sub"), |_| Opcode::Sub),
            map(tag("ter"), |_| Opcode::Ternary),
        ))(input)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_opcode_new() {
        assert_eq!(Opcode::new("add").unwrap().1, Opcode::Add);
        assert_eq!(Opcode::new("addc").unwrap().1, Opcode::AddChecked);
        assert_eq!(Opcode::new("addw").unwrap().1, Opcode::AddWrapped);
        assert_eq!(Opcode::new("and").unwrap().1, Opcode::And);
        assert_eq!(Opcode::new("eq").unwrap().1, Opcode::Eq);
        assert_eq!(Opcode::new("sub").unwrap().1, Opcode::Sub);
        assert_eq!(Opcode::new("subc").unwrap().1, Opcode::SubChecked);
        assert_eq!(Opcode::new("subw").unwrap().1, Opcode::SubWrapped);
        assert_eq!(Opcode::new("ter").unwrap().1, Opcode::Ternary);
    }

    #[test]
    fn test_invalid_opcode() {
        assert!(Opcode::new("jal").is_err());
    }
}
