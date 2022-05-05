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

macro_rules! impl_commit_evaluate {
    ($instruction:ident, $registers:ident) => {
        // Load the values for the first and second operands.
        let first = match $registers.load($instruction.operation.first()) {
            Value::Literal(literal) => literal.to_bits_le(),
            Value::Composite(_name, literals) => literals.iter().flat_map(|literal| literal.to_bits_le()).collect(),
        };
        let second = match $registers.load($instruction.operation.second()) {
            Value::Literal(literal) => literal,
            Value::Composite(name, ..) => P::halt(format!("{name} is not a literal")),
        };

        // Fetch the result from the program environment.
        let result = Literal::Group(P::Aleo::commit(Self::opcode(), &first, &second.to_bits_le()));

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
