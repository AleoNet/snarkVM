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

#[cfg(console)]
impl<A: Aleo> Literal<A> {
    /// Returns the type name of the literal.
    pub fn to_type(&self) -> console::LiteralType {
        match self {
            Self::Address(..) => console::LiteralType::Address,
            Self::Boolean(..) => console::LiteralType::Boolean,
            Self::Field(..) => console::LiteralType::Field,
            Self::Group(..) => console::LiteralType::Group,
            Self::I8(..) => console::LiteralType::I8,
            Self::I16(..) => console::LiteralType::I16,
            Self::I32(..) => console::LiteralType::I32,
            Self::I64(..) => console::LiteralType::I64,
            Self::I128(..) => console::LiteralType::I128,
            Self::U8(..) => console::LiteralType::U8,
            Self::U16(..) => console::LiteralType::U16,
            Self::U32(..) => console::LiteralType::U32,
            Self::U64(..) => console::LiteralType::U64,
            Self::U128(..) => console::LiteralType::U128,
            Self::Scalar(..) => console::LiteralType::Scalar,
            Self::String(..) => console::LiteralType::String,
        }
    }
}
