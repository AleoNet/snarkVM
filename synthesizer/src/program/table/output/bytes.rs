// Copyright (C) 2019-2023 Aleo Systems Inc.
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

impl<N: Network> FromBytes for TableOutput<N> {
    /// Reads the output statement from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the output type.
        let type_ = FromBytes::read_le(&mut reader)?;
        Ok(Self { type_ })
    }
}

impl<N: Network> ToBytes for TableOutput<N> {
    /// Writes the output statement to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the output type.
        self.type_.write_le(&mut writer)
    }
}
