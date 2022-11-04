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

impl<N: Network> FromBytes for MapKey<N> {
    /// Reads the key statement from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the key name.
        let name = FromBytes::read_le(&mut reader)?;
        // Read the key type.
        let finalize_type = FromBytes::read_le(&mut reader)?;
        // Return the key.
        Ok(Self { name, finalize_type })
    }
}

impl<N: Network> ToBytes for MapKey<N> {
    /// Writes the key statement to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the key name.
        self.name.write_le(&mut writer)?;
        // Write the key type.
        self.finalize_type.write_le(&mut writer)
    }
}
