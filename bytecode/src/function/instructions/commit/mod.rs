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

pub(crate) mod bhp256;
pub(crate) use bhp256::*;

pub(crate) mod bhp512;
pub(crate) use bhp512::*;

pub(crate) mod bhp1024;
pub(crate) use bhp1024::*;

pub(crate) mod ped64;
pub(crate) use ped64::*;

pub(crate) mod ped128;
pub(crate) use ped128::*;

use crate::{
    function::{parsers::*, Instruction, Opcode, Operation, Program, Register, Registers},
    Value,
};
use snarkvm_circuits::{Aleo, Literal, Parser, ParserResult, ToBits};
use snarkvm_utilities::{FromBytes, ToBytes};

use core::{fmt, marker::PhantomData};
use nom::combinator::map;
use std::io::{Read, Result as IoResult, Write};

pub trait CommitOpcode {
    const OPCODE: &'static str;
}

/// A generic commitment instruction.
pub struct Commit<P: Program, Op: CommitOpcode> {
    operation: BinaryOperation<P>,
    _phantom: PhantomData<Op>,
}

impl<P: Program, Op: CommitOpcode> Opcode for Commit<P, Op> {
    /// Returns the opcode as a string.
    #[inline]
    fn opcode() -> &'static str {
        Op::OPCODE
    }
}

impl<P: Program, Op: CommitOpcode> Commit<P, Op> {
    /// Returns the operands of the instruction.
    pub fn operands(&self) -> Vec<Operand<P>> {
        self.operation.operands()
    }

    /// Returns the destination register of the instruction.
    pub fn destination(&self) -> &Register<P> {
        self.operation.destination()
    }
}

impl<P: Program, Op: CommitOpcode> Operation<P> for Commit<P, Op> {
    /// Evaluates the operation.
    #[inline]
    fn evaluate(&self, registers: &Registers<P>) {
        // Load the input from the first operand.
        let input = registers.load(self.operation.first()).to_literals();
        // Load the randomizer from the second operand.
        let randomizer = match registers.load(self.operation.second()) {
            Value::Literal(literal) => literal,
            Value::Definition(name, ..) => P::halt(format!("{name} is not a literal")),
        };

        // Compute the digest for the given input.
        if let Literal::Scalar(randomizer) = randomizer {
            let commitment = match Self::opcode() {
                BHP256::OPCODE => P::Aleo::commit_bhp256(&input.to_bits_le(), &randomizer),
                BHP512::OPCODE => P::Aleo::commit_bhp512(&input.to_bits_le(), &randomizer),
                BHP1024::OPCODE => P::Aleo::commit_bhp1024(&input.to_bits_le(), &randomizer),
                Ped64::OPCODE => P::Aleo::commit_ped64(&input.to_bits_le(), &randomizer),
                Ped128::OPCODE => P::Aleo::commit_ped128(&input.to_bits_le(), &randomizer),
                _ => P::halt("Invalid option provided for the `commit` instruction"),
            };

            registers.assign(self.operation.destination(), Literal::Field(commitment));
        } else {
            P::halt("Invalid type provided for `randomness` in `commit` instruction")
        }
    }
}

impl<P: Program, Op: CommitOpcode> fmt::Display for Commit<P, Op> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.operation)
    }
}

impl<P: Program, Op: CommitOpcode> Parser for Commit<P, Op> {
    type Environment = P::Environment;

    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        map(BinaryOperation::parse, |operation| Self { operation, _phantom: PhantomData })(string)
    }
}

impl<P: Program, Op: CommitOpcode> FromBytes for Commit<P, Op> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self { operation: BinaryOperation::read_le(&mut reader)?, _phantom: PhantomData })
    }
}

impl<P: Program, Op: CommitOpcode> ToBytes for Commit<P, Op> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.operation.write_le(&mut writer)
    }
}

#[allow(clippy::from_over_into)]
impl<P: Program, Op: CommitOpcode> Into<Instruction<P>> for Commit<P, Op> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<P> {
        match Self::opcode() {
            BHP256::OPCODE => {
                Instruction::CommitBHP256(CommitBHP256 { operation: self.operation, _phantom: PhantomData })
            }
            BHP512::OPCODE => {
                Instruction::CommitBHP512(CommitBHP512 { operation: self.operation, _phantom: PhantomData })
            }
            BHP1024::OPCODE => {
                Instruction::CommitBHP1024(CommitBHP1024 { operation: self.operation, _phantom: PhantomData })
            }
            Ped64::OPCODE => Instruction::CommitPed64(CommitPed64 { operation: self.operation, _phantom: PhantomData }),
            Ped128::OPCODE => {
                Instruction::CommitPed128(CommitPed128 { operation: self.operation, _phantom: PhantomData })
            }
            _ => P::halt("Invalid option provided for the `commit` instruction"),
        }
    }
}
