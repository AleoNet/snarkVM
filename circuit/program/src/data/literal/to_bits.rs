// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;

impl<A: Aleo> ToBitsInto for Literal<A> {
    type Boolean = Boolean<A>;

    /// Returns the little-endian bits of the literal.
    fn to_bits_le_into(&self, vec: &mut Vec<<Literal<A> as ToBitsInto>::Boolean>) {
        (&self).to_bits_le_into(vec);
    }

    /// Returns the big-endian bits of the literal.
    fn to_bits_be_into(&self, vec: &mut Vec<<Literal<A> as ToBitsInto>::Boolean>) {
        (&self).to_bits_be_into(vec);
    }
}

impl<A: Aleo> ToBitsInto for &Literal<A> {
    type Boolean = Boolean<A>;

    /// Returns the little-endian bits of the literal.
    fn to_bits_le_into(&self, vec: &mut Vec<Self::Boolean>) {
        match self {
            Literal::Address(literal) => literal.to_bits_le_into(vec),
            Literal::Boolean(literal) => literal.to_bits_le_into(vec),
            Literal::Field(literal) => literal.to_bits_le_into(vec),
            Literal::Group(literal) => literal.to_bits_le_into(vec),
            Literal::I8(literal) => literal.to_bits_le_into(vec),
            Literal::I16(literal) => literal.to_bits_le_into(vec),
            Literal::I32(literal) => literal.to_bits_le_into(vec),
            Literal::I64(literal) => literal.to_bits_le_into(vec),
            Literal::I128(literal) => literal.to_bits_le_into(vec),
            Literal::U8(literal) => literal.to_bits_le_into(vec),
            Literal::U16(literal) => literal.to_bits_le_into(vec),
            Literal::U32(literal) => literal.to_bits_le_into(vec),
            Literal::U64(literal) => literal.to_bits_le_into(vec),
            Literal::U128(literal) => literal.to_bits_le_into(vec),
            Literal::Scalar(literal) => literal.to_bits_le_into(vec),
            Literal::String(literal) => literal.to_bits_le_into(vec),
        }
    }

    /// Returns the big-endian bits of the literal.
    fn to_bits_be_into(&self, vec: &mut Vec<Self::Boolean>) {
        match self {
            Literal::Address(literal) => literal.to_bits_be_into(vec),
            Literal::Boolean(literal) => literal.to_bits_be_into(vec),
            Literal::Field(literal) => literal.to_bits_be_into(vec),
            Literal::Group(literal) => literal.to_bits_be_into(vec),
            Literal::I8(literal) => literal.to_bits_be_into(vec),
            Literal::I16(literal) => literal.to_bits_be_into(vec),
            Literal::I32(literal) => literal.to_bits_be_into(vec),
            Literal::I64(literal) => literal.to_bits_be_into(vec),
            Literal::I128(literal) => literal.to_bits_be_into(vec),
            Literal::U8(literal) => literal.to_bits_be_into(vec),
            Literal::U16(literal) => literal.to_bits_be_into(vec),
            Literal::U32(literal) => literal.to_bits_be_into(vec),
            Literal::U64(literal) => literal.to_bits_be_into(vec),
            Literal::U128(literal) => literal.to_bits_be_into(vec),
            Literal::Scalar(literal) => literal.to_bits_be_into(vec),
            Literal::String(literal) => literal.to_bits_be_into(vec),
        }
    }
}
