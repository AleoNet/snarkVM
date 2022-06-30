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
    /// Returns the type name of the literal.
    pub fn to_type(&self) -> LiteralType {
        match self {
            Self::Address(..) => LiteralType::Address,
            Self::Boolean(..) => LiteralType::Boolean,
            Self::Field(..) => LiteralType::Field,
            Self::Group(..) => LiteralType::Group,
            Self::I8(..) => LiteralType::I8,
            Self::I16(..) => LiteralType::I16,
            Self::I32(..) => LiteralType::I32,
            Self::I64(..) => LiteralType::I64,
            Self::I128(..) => LiteralType::I128,
            Self::U8(..) => LiteralType::U8,
            Self::U16(..) => LiteralType::U16,
            Self::U32(..) => LiteralType::U32,
            Self::U64(..) => LiteralType::U64,
            Self::U128(..) => LiteralType::U128,
            Self::Scalar(..) => LiteralType::Scalar,
            Self::String(..) => LiteralType::String,
        }
    }
}
