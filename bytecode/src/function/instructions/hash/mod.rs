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
    function::{parsers::*, Instruction, Opcode, Operation, Registers},
    helpers::Register,
    Program,
    Value,
};
use snarkvm_circuits::{Aleo, Environment, FromBits, Literal, Parser, ParserResult, PrimeField, ToBits};
use snarkvm_utilities::{FromBytes, ToBytes};

use core::{fmt, marker::PhantomData};
use nom::combinator::map;
use std::io::{Read, Result as IoResult, Write};

pub trait Hasher: Opcode {}

const PED64: &str = "hash.ped64";

/// A generic hash instruction.
pub struct Hash<P: Program, O: Opcode> {
    operation: UnaryOperation<P>,
    _phantom: PhantomData<O>,
}

impl<P: Program, O: Opcode> Opcode for Hash<P, O> {
    /// Returns the opcode as a string.
    #[inline]
    fn opcode() -> &'static str {
        O::opcode()
    }
}

impl<P: Program, O: Opcode> Hash<P, O> {
    /// Returns the operands of the instruction.
    pub fn operands(&self) -> Vec<Operand<P>> {
        self.operation.operands()
    }

    /// Returns the destination register of the instruction.
    pub fn destination(&self) -> &Register<P> {
        self.operation.destination()
    }
}

impl<P: Program, O: Opcode> Operation<P> for Hash<P, O> {
    /// Evaluates the operation.
    #[inline]
    fn evaluate(&self, registers: &Registers<P>) {
        // Load the input from the operand.
        let input = match registers.load(self.operation.first()) {
            Value::Literal(literal) => literal.to_bits_le(),
            Value::Composite(_name, literals) => literals.iter().flat_map(|literal| literal.to_bits_le()).collect(),
        };

        // Compute the digest for the given input.
        let digest = match Self::opcode() {
            PED64 | "hash.ped128" | "hash.ped256" | "hash.ped512" | "hash.ped1024" => match Self::opcode() {
                PED64 => P::Aleo::pedersen_hash(Self::opcode(), &input),
                "hash.ped128" => P::Aleo::pedersen_hash(Self::opcode(), &input),
                "hash.ped256" => P::Aleo::pedersen_hash(Self::opcode(), &input),
                "hash.ped512" => P::Aleo::pedersen_hash(Self::opcode(), &input),
                "hash.ped1024" => P::Aleo::pedersen_hash(Self::opcode(), &input),
                _ => P::halt("Invalid option provided for the `hash` instruction"),
            },
            "hash.psd2" | "hash.psd4" | "hash.psd8" => {
                // Pack the input bits into field elements.
                let input_elements = input
                    .chunks(<P::Aleo as Environment>::BaseField::size_in_data_bits())
                    .map(FromBits::from_bits_le)
                    .collect::<Vec<_>>();

                // Compute the digest for the given input as field elements.
                match Self::opcode() {
                    "hash.psd2" => P::Aleo::poseidon_hash(Self::opcode(), &input_elements),
                    "hash.psd4" => P::Aleo::poseidon_hash(Self::opcode(), &input_elements),
                    "hash.psd8" => P::Aleo::poseidon_hash(Self::opcode(), &input_elements),
                    _ => P::halt("Invalid option provided for the `hash` instruction"),
                }
            }
            _ => P::halt("Invalid option provided for the `hash` instruction"),
        };

        registers.assign(self.operation.destination(), Literal::Field(digest));
    }
}

impl<P: Program, O: Opcode> fmt::Display for Hash<P, O> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.operation)
    }
}

impl<P: Program, O: Opcode> Parser for Hash<P, O> {
    type Environment = P::Environment;

    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        map(UnaryOperation::parse, |operation| Self { operation, _phantom: PhantomData })(string)
    }
}

impl<P: Program, O: Opcode> FromBytes for Hash<P, O> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self { operation: UnaryOperation::read_le(&mut reader)?, _phantom: PhantomData })
    }
}

impl<P: Program, O: Opcode> ToBytes for Hash<P, O> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.operation.write_le(&mut writer)
    }
}

#[allow(clippy::from_over_into)]
impl<P: Program, O: Opcode> Into<Instruction<P>> for Hash<P, O> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<P> {
        match Self::opcode() {
            "hash.ped64" => Instruction::HashPed64(HashPed64 { operation: self.operation, _phantom: PhantomData }),
            "hash.ped128" => Instruction::HashPed128(HashPed128 { operation: self.operation, _phantom: PhantomData }),
            "hash.ped256" => Instruction::HashPed256(HashPed256 { operation: self.operation, _phantom: PhantomData }),
            "hash.ped512" => Instruction::HashPed512(HashPed512 { operation: self.operation, _phantom: PhantomData }),
            "hash.ped1024" => {
                Instruction::HashPed1024(HashPed1024 { operation: self.operation, _phantom: PhantomData })
            }
            "hash.psd2" => Instruction::HashPsd2(HashPsd2 { operation: self.operation, _phantom: PhantomData }),
            "hash.psd4" => Instruction::HashPsd4(HashPsd4 { operation: self.operation, _phantom: PhantomData }),
            "hash.psd8" => Instruction::HashPsd8(HashPsd8 { operation: self.operation, _phantom: PhantomData }),
            _ => P::halt("Invalid option provided for the `hash` instruction"),
        }
    }
}
