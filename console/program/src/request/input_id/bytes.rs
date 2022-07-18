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

impl<N: Network> FromBytes for InputID<N> {
    /// Reads the input ID from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the variant.
        let variant = u8::read_le(&mut reader)?;
        // Match the variant.
        match variant {
            // Constant input.
            0 => Ok(Self::Constant(Field::read_le(&mut reader)?)),
            // Public input.
            1 => Ok(Self::Public(Field::read_le(&mut reader)?)),
            // Private input.
            2 => Ok(Self::Private(Field::read_le(&mut reader)?)),
            // Record input.
            3 => {
                // Read the gamma value.
                let gamma = Group::read_le(&mut reader)?;
                // Read the serial number.
                let serial = Field::read_le(&mut reader)?;
                // Return the record input.
                Ok(Self::Record(gamma, serial))
            }
            // External record input.
            4 => Ok(Self::ExternalRecord(Field::read_le(&mut reader)?)),
            // Invalid input.
            _ => Err(error("Invalid input ID variant")),
        }
    }
}

impl<N: Network> ToBytes for InputID<N> {
    /// Writes the input ID to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        match self {
            // Constant input.
            Self::Constant(value) => {
                // Write the variant.
                0u8.write_le(&mut writer)?;
                // Write the value.
                value.write_le(&mut writer)
            }
            // Public input.
            Self::Public(value) => {
                // Write the variant.
                1u8.write_le(&mut writer)?;
                // Write the value.
                value.write_le(&mut writer)
            }
            // Private input.
            Self::Private(value) => {
                // Write the variant.
                2u8.write_le(&mut writer)?;
                // Write the value.
                value.write_le(&mut writer)
            }
            // Record input.
            Self::Record(gamma, serial) => {
                // Write the variant.
                3u8.write_le(&mut writer)?;
                // Write the gamma value.
                gamma.write_le(&mut writer)?;
                // Write the serial number.
                serial.write_le(&mut writer)
            }
            // External record input.
            Self::ExternalRecord(value) => {
                // Write the variant.
                4u8.write_le(&mut writer)?;
                // Write the value.
                value.write_le(&mut writer)
            }
        }
    }
}
