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

use super::*;

impl<N: Network> Literal<N> {
    /// Returns a randomly-sampled literal of the given literal type.
    pub fn sample<R: Rng + CryptoRng>(literal_type: LiteralType, rng: &mut R) -> Self {
        match literal_type {
            LiteralType::Address => Literal::Address(Address::new(Group::rand(rng))),
            LiteralType::Boolean => Literal::Boolean(Boolean::rand(rng)),
            LiteralType::Field => Literal::Field(Field::rand(rng)),
            LiteralType::Group => Literal::Group(Group::rand(rng)),
            LiteralType::I8 => Literal::I8(I8::rand(rng)),
            LiteralType::I16 => Literal::I16(I16::rand(rng)),
            LiteralType::I32 => Literal::I32(I32::rand(rng)),
            LiteralType::I64 => Literal::I64(I64::rand(rng)),
            LiteralType::I128 => Literal::I128(I128::rand(rng)),
            LiteralType::U8 => Literal::U8(U8::rand(rng)),
            LiteralType::U16 => Literal::U16(U16::rand(rng)),
            LiteralType::U32 => Literal::U32(U32::rand(rng)),
            LiteralType::U64 => Literal::U64(U64::rand(rng)),
            LiteralType::U128 => Literal::U128(U128::rand(rng)),
            LiteralType::Scalar => Literal::Scalar(Scalar::rand(rng)),
            LiteralType::String => Literal::String(StringType::rand(rng)),
        }
    }
}
