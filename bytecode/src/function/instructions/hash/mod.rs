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

pub(crate) mod ped256;
pub(crate) use ped256::*;

pub(crate) mod ped512;
pub(crate) use ped512::*;

pub(crate) mod ped1024;
pub(crate) use ped1024::*;

pub(crate) mod psd2;
pub(crate) use psd2::*;

pub(crate) mod psd4;
pub(crate) use psd4::*;

pub(crate) mod psd8;
pub(crate) use psd8::*;

use crate::{
    function::{parsers::*, Instruction, Opcode, Operation, Register, Registers},
    Program,
};
use snarkvm_circuits::{Aleo, Environment, FromBits, Literal, Parser, ParserResult, PrimeField, ToBits, ToField};
use snarkvm_utilities::{FromBytes, ToBytes};

use core::{fmt, marker::PhantomData};
use nom::combinator::map;
use std::io::{Read, Result as IoResult, Write};

pub trait HashOpcode {
    const OPCODE: &'static str;
}

/// A generic hash instruction.
pub struct Hash<P: Program, Op: HashOpcode> {
    operation: UnaryOperation<P>,
    _phantom: PhantomData<Op>,
}

impl<P: Program, Op: HashOpcode> Opcode for Hash<P, Op> {
    /// Returns the opcode as a string.
    #[inline]
    fn opcode() -> &'static str {
        Op::OPCODE
    }
}

impl<P: Program, Op: HashOpcode> Hash<P, Op> {
    /// Returns the operands of the instruction.
    pub fn operands(&self) -> Vec<Operand<P>> {
        self.operation.operands()
    }

    /// Returns the destination register of the instruction.
    pub fn destination(&self) -> &Register<P> {
        self.operation.destination()
    }
}

impl<P: Program, Op: HashOpcode> Operation<P> for Hash<P, Op> {
    /// Evaluates the operation.
    #[inline]
    fn evaluate(&self, registers: &Registers<P>) {
        // Load the input from the operand.
        let input = registers.load(self.operation.first()).to_literals();

        // TODO (howardwu): Implement `Literal::to_fields()` to replace this closure.
        // (Optional) Closure for converting a list of literals into a list of field elements.
        //
        // If the list is comprised of `Address`, `Field`, `Group`, and/or `Scalar`, then the closure
        // will return the underlying field elements (instead of packing the literals from bits).
        // Otherwise, the list is converted into bits, and then packed into field elements.
        let to_field_elements = |input: &[Literal<_>]| {
            // Determine whether the input is comprised of field-friendly literals.
            match input.iter().all(|literal| {
                matches!(literal, Literal::Address(_) | Literal::Field(_) | Literal::Group(_) | Literal::Scalar(_))
            }) {
                // Case 1 - Map each literal directly to its field representation.
                true => input
                    .iter()
                    .map(|literal| match literal {
                        Literal::Address(address) => address.to_field(),
                        Literal::Field(field) => field.clone(),
                        Literal::Group(group) => group.to_x_coordinate(),
                        Literal::Scalar(scalar) => scalar.to_field(),
                        _ => P::halt("Unreachable literal variant detected during hashing."),
                    })
                    .collect::<Vec<_>>(),
                // Case 2 - Convert the literals to bits, and then pack them into field elements.
                false => input
                    .to_bits_le()
                    .chunks(<P::Environment as Environment>::BaseField::size_in_data_bits())
                    .map(FromBits::from_bits_le)
                    .collect::<Vec<_>>(),
            }
        };

        // Compute the digest for the given input.
        let digest = match Self::opcode() {
            BHP256::OPCODE => P::Aleo::hash_bhp256(&input.to_bits_le()),
            BHP512::OPCODE => P::Aleo::hash_bhp512(&input.to_bits_le()),
            BHP1024::OPCODE => P::Aleo::hash_bhp1024(&input.to_bits_le()),
            Ped64::OPCODE => P::Aleo::hash_ped64(&input.to_bits_le()),
            Ped128::OPCODE => P::Aleo::hash_ped128(&input.to_bits_le()),
            Ped256::OPCODE => P::Aleo::hash_ped256(&input.to_bits_le()),
            Ped512::OPCODE => P::Aleo::hash_ped512(&input.to_bits_le()),
            Ped1024::OPCODE => P::Aleo::hash_ped1024(&input.to_bits_le()),
            Psd2::OPCODE => P::Aleo::hash_psd2(&to_field_elements(&input)),
            Psd4::OPCODE => P::Aleo::hash_psd4(&to_field_elements(&input)),
            Psd8::OPCODE => P::Aleo::hash_psd8(&to_field_elements(&input)),
            _ => P::halt("Invalid option provided for the `hash` instruction"),
        };

        registers.assign(self.operation.destination(), Literal::Field(digest));
    }
}

impl<P: Program, Op: HashOpcode> fmt::Display for Hash<P, Op> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.operation)
    }
}

impl<P: Program, Op: HashOpcode> Parser for Hash<P, Op> {
    type Environment = P::Environment;

    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        map(UnaryOperation::parse, |operation| Self { operation, _phantom: PhantomData })(string)
    }
}

impl<P: Program, Op: HashOpcode> FromBytes for Hash<P, Op> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self { operation: UnaryOperation::read_le(&mut reader)?, _phantom: PhantomData })
    }
}

impl<P: Program, Op: HashOpcode> ToBytes for Hash<P, Op> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.operation.write_le(&mut writer)
    }
}

#[allow(clippy::from_over_into)]
impl<P: Program, Op: HashOpcode> Into<Instruction<P>> for Hash<P, Op> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<P> {
        match Self::opcode() {
            BHP256::OPCODE => Instruction::HashBHP256(HashBHP256 { operation: self.operation, _phantom: PhantomData }),
            BHP512::OPCODE => Instruction::HashBHP512(HashBHP512 { operation: self.operation, _phantom: PhantomData }),
            BHP1024::OPCODE => {
                Instruction::HashBHP1024(HashBHP1024 { operation: self.operation, _phantom: PhantomData })
            }
            Ped64::OPCODE => Instruction::HashPed64(HashPed64 { operation: self.operation, _phantom: PhantomData }),
            Ped128::OPCODE => Instruction::HashPed128(HashPed128 { operation: self.operation, _phantom: PhantomData }),
            Ped256::OPCODE => Instruction::HashPed256(HashPed256 { operation: self.operation, _phantom: PhantomData }),
            Ped512::OPCODE => Instruction::HashPed512(HashPed512 { operation: self.operation, _phantom: PhantomData }),
            Ped1024::OPCODE => {
                Instruction::HashPed1024(HashPed1024 { operation: self.operation, _phantom: PhantomData })
            }
            Psd2::OPCODE => Instruction::HashPsd2(HashPsd2 { operation: self.operation, _phantom: PhantomData }),
            Psd4::OPCODE => Instruction::HashPsd4(HashPsd4 { operation: self.operation, _phantom: PhantomData }),
            Psd8::OPCODE => Instruction::HashPsd8(HashPsd8 { operation: self.operation, _phantom: PhantomData }),
            _ => P::halt("Invalid option provided for the `hash` instruction"),
        }
    }
}
