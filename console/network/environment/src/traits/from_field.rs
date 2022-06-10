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

use super::FieldTrait;

use anyhow::Result;

/// Unary operator for converting from a base field element.
pub trait FromField {
    type Field: FieldTrait;

    /// Initializes an object from a base field element.
    fn from_field(field: &Self::Field) -> Result<Self>
    where
        Self: Sized;
}

/// Unary operator for converting from a list of base elements.
pub trait FromFields {
    type Field: FieldTrait;

    /// Initializes an object from a list of base field elements.
    fn from_fields(fields: &[Self::Field]) -> Result<Self>
    where
        Self: Sized;
}
