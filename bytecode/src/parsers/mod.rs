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

use crate::{Instruction, Memory, Opcode, Operand, Register};

use snarkvm_circuits::{Environment, Parser, ParserResult};

use nom::{
    branch::alt,
    bytes::complete::tag,
    combinator::{map, verify},
};

pub type UnaryParser<M> = InstructionParser<M, 1>;
pub type BinaryParser<M> = InstructionParser<M, 2>;
pub type TernaryParser<M> = InstructionParser<M, 3>;

pub struct InstructionParser<M: Memory, const NAME: &'static str, const N: usize>(PhantomData<M>);

impl<M: Memory, const NAME: &'static str, const N: usize> Parser for InstructionParser<M, NAME, N> {
    type Environment = M::Environment;
    type Output = (Opcode, Register<M::Environment>, Vec<Operand<M>>);

    /// Parses the components of an n-ary instruction.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self::Output> {
        // Parse the opcode
        let (string, opcode) = verify(Opcode::new, |op| op.arity() == N)(string)?;
        // Parse the destination register from the string.
        let (string, destination_register) = Register::parse(string)?;
        // Parse the appropriate number of operand from the string.
        let mut operands = Vec::with_capacity(N);
        let mut string = string;
        for _ in 0..N {
            let (s, operand) = Operand::parse(string)?;
            string = s;
            operands.push(operand)
        }
        // Parse the semicolon from the string.
        let (string, _) = tag(";")(string)?;

        Ok((string, (opcode, destination_register, operands)))
    }
}
