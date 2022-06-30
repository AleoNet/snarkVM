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

impl<N: Network> ToFields for Plaintext<N> {
    type Field = Field<N>;

    /// Returns this plaintext as a list of field elements.
    fn to_fields(&self) -> Result<Vec<Self::Field>> {
        // Encode the data as little-endian bits.
        let mut bits_le = self.to_bits_le();
        // Adds one final bit to the data, to serve as a terminus indicator.
        // During decryption, this final bit ensures we've reached the end.
        bits_le.push(true);
        // Pack the bits into field elements.
        let fields = bits_le
            .chunks(Field::<N>::size_in_data_bits())
            .map(Field::<N>::from_bits_le)
            .collect::<Result<Vec<_>>>()?;
        // Ensure the number of field elements does not exceed the maximum allowed size.
        match fields.len() <= N::MAX_DATA_SIZE_IN_FIELDS as usize {
            true => Ok(fields),
            false => bail!("Plaintext exceeds maximum allowed size"),
        }
    }
}
