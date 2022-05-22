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

impl<A: Aleo> ToFields for Literal<A> {
    type Field = Field<A>;

    /// Returns the literal as a list of base field elements.
    fn to_fields(&self) -> Vec<Field<A>> {
        (&self).to_fields()
    }
}

impl<A: Aleo> ToFields for &Literal<A> {
    type Field = Field<A>;

    /// Returns the literal as a list of base field elements.
    fn to_fields(&self) -> Vec<Self::Field> {
        match self {
            Literal::Address(literal) => vec![literal.to_field()],
            Literal::Boolean(literal) => vec![Field::from_boolean(literal)],
            Literal::Field(literal) => vec![literal.clone()],
            Literal::Group(literal) => vec![literal.to_x_coordinate()],
            Literal::I8(literal) => vec![literal.to_field()],
            Literal::I16(literal) => vec![literal.to_field()],
            Literal::I32(literal) => vec![literal.to_field()],
            Literal::I64(literal) => vec![literal.to_field()],
            Literal::I128(literal) => vec![literal.to_field()],
            Literal::U8(literal) => vec![literal.to_field()],
            Literal::U16(literal) => vec![literal.to_field()],
            Literal::U32(literal) => vec![literal.to_field()],
            Literal::U64(literal) => vec![literal.to_field()],
            Literal::U128(literal) => vec![literal.to_field()],
            Literal::Scalar(literal) => vec![literal.to_field()],
            Literal::String(literal) => literal.to_fields(),
        }
    }
}
