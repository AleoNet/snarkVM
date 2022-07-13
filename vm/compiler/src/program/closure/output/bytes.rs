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

impl<N: Network> FromBytes for Output<N> {
    /// Reads the output from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let register = FromBytes::read_le(&mut reader)?;
        let register_type = FromBytes::read_le(&mut reader)?;
        Ok(Self { register, register_type })
    }
}

impl<N: Network> ToBytes for Output<N> {
    /// Writes the output to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.register.write_le(&mut writer)?;
        self.register_type.write_le(&mut writer)
    }
}
