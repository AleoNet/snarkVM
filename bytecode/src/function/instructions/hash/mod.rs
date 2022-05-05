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

macro_rules! impl_pedersen_evaluate {
    ($instruction:ident, $registers:ident) => {
        // Load the values for the first and second operands.
        let first = match $registers.load($instruction.operation.first()) {
            Value::Literal(literal) => literal.to_bits_le(),
            Value::Composite(_name, literals) => literals.iter().flat_map(|literal| literal.to_bits_le()).collect(),
        };

        // Fetch the result from the program environment.
        let result = Literal::Field(P::Aleo::pedersen_hash(Self::opcode(), &first));

        $registers.assign($instruction.operation.destination(), result);
    };
}

macro_rules! impl_poseidon_evaluate {
    ($instruction:ident, $registers:ident) => {
        // Load the values for the first and second operands.
        let first = match $registers.load($instruction.operation.first()) {
            Value::Literal(literal) => vec![literal],
            Value::Composite(_name, literals) => literals,
        };

        let first = first
            .into_iter()
            .flat_map(|literal| match literal {
                Literal::Field(a) => vec![a],
                Literal::I8(a) => a.to_fields(),
                Literal::I16(a) => a.to_fields(),
                Literal::I32(a) => a.to_fields(),
                Literal::I64(a) => a.to_fields(),
                Literal::I128(a) => a.to_fields(),
                Literal::U8(a) => a.to_fields(),
                Literal::U16(a) => a.to_fields(),
                Literal::U32(a) => a.to_fields(),
                Literal::U64(a) => a.to_fields(),
                Literal::U128(a) => a.to_fields(),
                Literal::Scalar(a) => a.to_fields(),
                Literal::String(a) => a.to_fields(),
                _ => P::halt(format!("Invalid '{}' instruction", Self::opcode())),
            })
            .collect::<Vec<Field<P::Environment>>>();

        // Fetch the result from the program environment.
        let result = Literal::Field(P::Aleo::poseidon_hash(Self::opcode(), &first));

        $registers.assign($instruction.operation.destination(), result);
    };
}

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
