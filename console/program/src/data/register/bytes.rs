// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

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
            2 => {
                // Read the number of indices.
                let num_indices = match u8::read_le(&mut reader)? {
                    index if index as usize <= N::MAX_DATA_DEPTH => index,
                    _ => {
                        return Err(error(format!(
                            "Failed to deserialize register: number of indices exceeds '{}'",
                            N::MAX_DATA_DEPTH
                        )));
                    }
                };
                // Read the indices.
                let mut indices = Vec::with_capacity(num_indices as usize);
                for _ in 0..num_indices {
                    indices.push(u32::read_le(&mut reader)?);
                }
                Ok(Self::Index(locator, indices))
            }
            3.. => Err(error(format!("Failed to deserialize register variant {variant}"))),
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
                // Ensure the number of identifiers is within the limit.
                if identifiers.len() > N::MAX_DATA_DEPTH {
                    return Err(error("Failed to serialize register: too many identifiers"));
                }

                u8::write_le(&1u8, &mut writer)?;
                variable_length_integer(locator).write_le(&mut writer)?;
                u16::try_from(identifiers.len())
                    .or_halt_with::<N>("Register path length exceeds u16::MAX")
                    .write_le(&mut writer)?;
                identifiers.write_le(&mut writer)
            }
            Self::Index(locator, indices) => {
                // Ensure the number of indices is within the limit.
                if indices.len() > N::MAX_DATA_DEPTH {
                    return Err(error("Failed to serialize register: too many indices"));
                }

                u8::write_le(&2u8, &mut writer)?;
                variable_length_integer(locator).write_le(&mut writer)?;
                u8::try_from(indices.len())
                    .or_halt_with::<N>("Register index count exceeds u8::MAX")
                    .write_le(&mut writer)?;
                indices.write_le(&mut writer)
            }
        }
    }
}
