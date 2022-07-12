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

impl<N: Network> ToBytes for RegisterType<N> {
    /// Writes the register type to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        (self.enum_index() as u8).write_le(&mut writer)?;
        match self {
            Self::Plaintext(plaintext_type) => plaintext_type.write_le(&mut writer),
            Self::Record(identifier) => identifier.write_le(&mut writer),
            Self::ExternalRecord(locator) => locator.write_le(&mut writer),
        }
    }
}

impl<N: Network> FromBytes for RegisterType<N> {
    /// Reads the register type from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let variant = u8::read_le(&mut reader)?;
        match variant {
            0 => Ok(Self::Plaintext(PlaintextType::read_le(&mut reader)?)),
            1 => Ok(Self::Record(Identifier::read_le(&mut reader)?)),
            2 => Ok(Self::ExternalRecord(Locator::read_le(&mut reader)?)),
            3.. => Err(error(format!("Failed to deserialize register type variant {}", variant))),
        }
    }
}
