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

use crate::{LiteralType, Program};

use snarkvm_circuits::{ConstantOrMode, Field, Literal};

/// Helper enum used to propagate static type information through bytecode.
#[derive(Debug, Clone)]
pub enum LiteralOrType<P: Program> {
    Literal(Literal<P::Environment>),
    Type(LiteralType<P>),
}

impl<P: Program> LiteralOrType<P> {
    pub fn type_(&self) -> LiteralType<P> {
        match self {
            LiteralOrType::Literal(literal) => literal.into(),
            LiteralOrType::Type(literal_type) => *literal_type,
        }
    }
}

/// Initializes a new `ModeOrConstant` from a `LiteralOrType`.
impl<P: Program> From<&LiteralOrType<P>> for ConstantOrMode<Field<P::Environment>> {
    fn from(literal_or_type: &LiteralOrType<P>) -> Self {
        match literal_or_type {
            LiteralOrType::Literal(Literal::Field(field)) => ConstantOrMode::from(field),
            LiteralOrType::Type(literal_type) => ConstantOrMode::Mode(*literal_type.mode()),
            _ => P::halt("Cannot convert literal or type to ConstantOrMode<Field<E>>"),
        }
    }
}
