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

impl<N: Network> FromBytes for Register<N> {
    /// Reads the register from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let variant = u8::read_le(&mut reader)?;
        let locator = read_variable_length_integer(&mut reader)?;
        match variant {
            0 => Ok(Self::Locator(locator)),
            1 => {
                // Read the number of identifiers.
                let num_identifiers = u16::read_le(&mut reader)?;
                // Read the identifiers.
                let mut identifiers = Vec::with_capacity(num_identifiers as usize);
                for _ in 0..num_identifiers {
                    identifiers.push(Identifier::read_le(&mut reader)?);
                }
                Ok(Self::Member(locator, identifiers))
            }
            2.. => Err(error(format!("Failed to deserialize register variant {variant}"))),
        }
    }
}

impl<N: Network> ToBytes for Register<N> {
    /// Writes the register to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        match self {
            Self::Locator(locator) => {
                u8::write_le(&0u8, &mut writer)?;
                variable_length_integer(locator).write_le(&mut writer)
            }
            Self::Member(locator, identifiers) => {
                // Ensure the number of identifiers is within `N::MAX_DATA_DEPTH`.
                if identifiers.len() > N::MAX_DATA_DEPTH {
                    return Err(error("Failed to serialize register: too many identifiers"));
                }

                u8::write_le(&1u8, &mut writer)?;
                variable_length_integer(locator).write_le(&mut writer)?;
                (identifiers.len() as u16).write_le(&mut writer)?;
                identifiers.write_le(&mut writer)
            }
        }
    }
}
