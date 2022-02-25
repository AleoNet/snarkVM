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

use crate::{Operand, Operation, ParserResult, Register, Type};
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
    operation: Operation,
    sources: Vec<Operand<E>>,
    destinations: Vec<Register>,
}

impl<E: Environment> Instruction<E> {
    pub fn new(input: &str) -> ParserResult<Self> {
        let (input, destinations) = separated_list0(tag(", "), Register::new)(input)?;
        let (input, _) = tag(" := ")(input)?;
        let (input, operation) = Operation::new(input)?;
        let (input, _) = tag(" ")(input)?;
        let (input, sources) = separated_list0(tag(", "), Operand::<E>::new)(input)?;
        let (input, _) = tag(";")(input)?;
        Ok((input, Self { operation, sources, destinations }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::Opcode;
    use snarkvm_circuits::Circuit;

    #[test]
    fn test_add_instruction() {
        type E = Circuit;
        let (_, instruction) = Instruction::<E>::new("base.r3 := add.base base.r2, base.r1;").unwrap();
        assert_eq!(instruction.operation.get_opcode(), Opcode::Add);
    }
}
