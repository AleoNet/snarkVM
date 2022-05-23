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

#[derive(Clone)]
pub struct Ciphertext<N: Network>(pub(in crate::program::entry) Vec<N::Field>);

impl<N: Network> Visibility<N> for Ciphertext<N> {
    /// Returns the number of field elements to encode `self`.
    fn size_in_fields(&self) -> usize {
        self.0.len()
    }
}

impl<N: Network> ToFields for Ciphertext<N> {
    type Field = N::Field;

    /// Returns this ciphertext as a list of field elements.
    fn to_fields(&self) -> Result<Vec<Self::Field>> {
        Ok(self.0.clone())
    }
}

impl<N: Network> FromFields for Ciphertext<N> {
    type Field = N::Field;

    /// Creates ciphertext from a list of field elements.
    fn from_fields(fields: &[Self::Field]) -> Result<Self> {
        Ok(Ciphertext(fields.to_vec()))
    }
}

impl<N: Network> ToBits for Ciphertext<N> {
    /// Returns this entry as a list of **little-endian** bits.
    fn to_bits_le(&self) -> Vec<bool> {
        let bits_le = self.0.to_bits_le();
        assert_eq!(self.0.len() * N::Field::size_in_bits(), bits_le.len());
        bits_le
    }

    /// Returns this entry as a list of **big-endian** bits.
    fn to_bits_be(&self) -> Vec<bool> {
        let bits_be = self.0.to_bits_be();
        assert_eq!(self.0.len() * N::Field::size_in_bits(), bits_be.len());
        bits_be
    }
}

impl<N: Network> FromBits for Ciphertext<N> {
    /// Returns this entry as a list of **little-endian** bits.
    fn from_bits_le(bits_le: &[bool]) -> Result<Self> {
        Ok(Self(
            bits_le
                .chunks(N::Field::size_in_bits())
                .map(|chunk| N::field_from_bits_le(chunk))
                .collect::<Result<Vec<_>>>()?,
        ))
    }

    /// Returns this entry as a list of **big-endian** bits.
    fn from_bits_be(bits_be: &[bool]) -> Result<Self> {
        Ok(Self(
            bits_be
                .chunks(N::Field::size_in_bits())
                .map(|chunk| N::field_from_bits_be(chunk))
                .collect::<Result<Vec<_>>>()?,
        ))
    }
}

impl<N: Network> Deref for Ciphertext<N> {
    type Target = [N::Field];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
