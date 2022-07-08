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

impl<N: Network> FromBytes for Locator<N> {
    /// Reads the locator from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let id = FromBytes::read_le(&mut reader)?;
        let resource = FromBytes::read_le(&mut reader)?;
        Ok(Self { id, resource })
    }
}

impl<N: Network> ToBytes for Locator<N> {
    /// Writes the locator to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.id.write_le(&mut writer)?;
        self.resource.write_le(&mut writer)
    }
}
