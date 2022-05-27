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

use crate::{BooleanTrait, FieldTrait, GroupTrait, ScalarTrait};

/// Unary operator for converting to `k` number of bits.
pub trait ToLowerBits {
    type Boolean: BooleanTrait;

    ///
    /// Outputs the lower `k` bits of an `n`-bit element in little-endian representation.
    /// Enforces that the upper `n - k` bits are zero.
    ///
    fn to_lower_bits_le(&self, k: usize) -> Vec<Self::Boolean>;

    ///
    /// Outputs the lower `k` bits of an `n`-bit element in big-endian representation.
    /// Enforces that the upper `n - k` bits are zero.
    ///
    fn to_lower_bits_be(&self, k: usize) -> Vec<Self::Boolean>;
}

/// Unary operator for converting to `k` number of bits.
pub trait ToUpperBits {
    type Boolean: BooleanTrait;

    ///
    /// Outputs the upper `k` bits of an `n`-bit element in little-endian representation.
    /// Enforces that the lower `n - k` bits are zero.
    ///
    fn to_upper_bits_le(&self, k: usize) -> Vec<Self::Boolean>;

    ///
    /// Outputs the upper `k` bits of an `n`-bit element in big-endian representation.
    /// Enforces that the lower `n - k` bits are zero.
    ///
    fn to_upper_bits_be(&self, k: usize) -> Vec<Self::Boolean>;
}

/// Unary operator for converting to a base field.
pub trait ToField {
    type Field: FieldTrait;

    /// Returns a circuit as a base field element.
    fn to_field(&self) -> Self::Field;
}

/// Unary operator for converting to a list of base fields.
pub trait ToFields {
    type Field: FieldTrait;

    /// Returns the circuit as a list of base field elements.
    fn to_fields(&self) -> Vec<Self::Field>;
}

/// Unary operator for converting to an affine group.
pub trait ToGroup {
    type Group: GroupTrait<Self::Scalar>;
    type Scalar: ScalarTrait;

    /// Returns the circuit as a list of affine group elements.
    fn to_group(&self) -> Self::Group;
}
