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

use crate::{Instruction, ParserResult};
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{char, one_of},
    combinator::verify,
    error::{make_error, ErrorKind, VerboseError, VerboseErrorKind},
    multi::{many0, many1, separated_list0},
    sequence::terminated,
};
use snarkvm_circuits::{Environment, IntegerType};

pub struct Program {
    pub(crate) instructions: Vec<Instruction>,
}

// TODO (@pranav) Accept more separators as needed.
impl Program {
    pub fn new(input: &str) -> ParserResult<Self> {
        let (input, instructions) = separated_list0(alt((tag(" "), tag("\n"))), Instruction::new)(input)?;
        Ok((input, Self { instructions }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::str::FromStr;
    use snarkvm_circuits::Circuit;

    #[test]
    fn test_program_new() {
        let (input, program) = Program::new(
            "u8.r3 := addw.u8 u8.r2, u8.r1; u8.r6 := addw.u8 u8.r5, u8.r4; bool.r1 := eq.u8 u8.r5, u8.r6;",
        )
        .unwrap();
        assert_eq!(3, program.instructions.len());

        let (input, program) = Program::new(
            "u8.r3 := addw.u8 u8.r2, u8.r1;\n\
                   u8.r6 := addw.u8 u8.r5, u8.r4;\n\
                   bool.r1 := eq.u8 u8.r5, u8.r6;",
        )
        .unwrap();
        assert_eq!(3, program.instructions.len());
    }
}
