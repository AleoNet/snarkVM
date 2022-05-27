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

impl<A: Aleo> From<Vec<Field<A>>> for Plaintext<A> {
    /// Initializes a plaintext from a list of base field elements.
    fn from(fields: Vec<Field<A>>) -> Self {
        Self::from_fields(&fields)
    }
}

impl<A: Aleo> From<&[Field<A>]> for Plaintext<A> {
    /// Initializes a plaintext from a list of base field elements.
    fn from(fields: &[Field<A>]) -> Self {
        Self::from_fields(fields)
    }
}

impl<A: Aleo> FromFields for Plaintext<A> {
    type Field = Field<A>;

    /// Initializes a plaintext from a list of base field elements.
    fn from_fields(fields: &[Self::Field]) -> Self {
        // Ensure the number of field elements does not exceed the maximum allowed size.
        if fields.len() > A::MAX_DATA_SIZE_IN_FIELDS as usize {
            A::halt("Plaintext exceeds maximum allowed size")
        }

        // Unpack the field elements into little-endian bits, and reverse the list for popping the terminus bit off.
        let mut bits_le =
            fields.iter().flat_map(|field| field.to_bits_le()[..A::BaseField::size_in_data_bits()].to_vec()).rev();
        // Remove the terminus bit that was added during encoding.
        for boolean in bits_le.by_ref() {
            // Drop all extraneous `0` bits, in addition to the final `1` bit.
            if boolean.eject_value() {
                // This case will always be reached, since the terminus bit is always `1`.
                break;
            }
        }
        // Reverse the bits back and recover the data from the bits.
        Self::from_bits_le(&bits_le.rev().collect::<Vec<_>>())
    }
}
