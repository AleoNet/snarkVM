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

use core::ops::Deref;

#[derive(Clone)]
pub struct Ciphertext<A: Aleo>(pub(in crate::program::entry) Vec<Field<A>>);

impl<A: Aleo> Visibility<A> for Ciphertext<A> {
    /// Returns the number of field elements to encode `self`.
    fn size_in_fields(&self) -> u16 {
        // Retrieve the number of field elements.
        let num_fields = self.0.len();
        match num_fields < A::MAX_DATA_SIZE_IN_FIELDS as usize {
            // Return the number of field elements.
            true => num_fields as u16,
            false => A::halt("Ciphertext is too large to encode in field elements."),
        }
    }
}

impl<A: Aleo> ToFields for Ciphertext<A> {
    type Field = Field<A>;

    /// Returns this ciphertext as a list of field elements.
    fn to_fields(&self) -> Vec<Self::Field> {
        self.0.clone()
    }
}

impl<A: Aleo> FromFields for Ciphertext<A> {
    type Field = Field<A>;

    /// Creates ciphertext from a list of field elements.
    fn from_fields(fields: &[Self::Field]) -> Self {
        Ciphertext(fields.to_vec())
    }
}

impl<A: Aleo> ToBits for Ciphertext<A> {
    type Boolean = Boolean<A>;

    /// Returns this entry as a list of **little-endian** bits.
    fn to_bits_le(&self) -> Vec<Self::Boolean> {
        let bits_le = self.0.to_bits_le();
        assert_eq!(self.0.len() * A::BaseField::size_in_bits(), bits_le.len());
        bits_le
    }

    /// Returns this entry as a list of **big-endian** bits.
    fn to_bits_be(&self) -> Vec<Self::Boolean> {
        let bits_be = self.0.to_bits_be();
        assert_eq!(self.0.len() * A::BaseField::size_in_bits(), bits_be.len());
        bits_be
    }
}

impl<A: Aleo> FromBits for Ciphertext<A> {
    type Boolean = Boolean<A>;

    /// Returns this entry as a list of **little-endian** bits.
    fn from_bits_le(bits_le: &[Self::Boolean]) -> Self {
        Self(bits_le.chunks(A::BaseField::size_in_bits()).map(Field::from_bits_le).collect())
    }

    /// Returns this entry as a list of **big-endian** bits.
    fn from_bits_be(bits_be: &[Self::Boolean]) -> Self {
        Self(bits_be.chunks(A::BaseField::size_in_bits()).map(Field::from_bits_be).collect())
    }
}

impl<A: Aleo> Deref for Ciphertext<A> {
    type Target = [Field<A>];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
