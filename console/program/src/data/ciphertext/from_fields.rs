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

impl<N: Network> TryFrom<Vec<Field<N>>> for Ciphertext<N> {
    type Error = Error;

    /// Initializes a ciphertext from a list of base field elements.
    fn try_from(fields: Vec<Field<N>>) -> Result<Self, Self::Error> {
        // Ensure the number of field elements does not exceed the maximum allowed size.
        match fields.len() <= N::MAX_DATA_SIZE_IN_FIELDS as usize {
            true => Ok(Self(fields)),
            false => bail!("Ciphertext exceeds maximum allowed size"),
        }
    }
}

impl<N: Network> TryFrom<&[Field<N>]> for Ciphertext<N> {
    type Error = Error;

    /// Initializes a ciphertext from a list of base field elements.
    fn try_from(fields: &[Field<N>]) -> Result<Self, Self::Error> {
        Self::from_fields(fields)
    }
}

impl<N: Network> FromFields for Ciphertext<N> {
    type Field = Field<N>;

    /// Initializes a ciphertext from a list of base field elements.
    fn from_fields(fields: &[Self::Field]) -> Result<Self> {
        Self::try_from(fields.to_vec())
    }
}
