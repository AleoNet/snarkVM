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

impl<N: Network> FromBytes for Access<N> {
    /// Reads the access from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self>
    where
        Self: Sized,
    {
        let variant = u8::read_le(&mut reader)?;
        match variant {
            0 => Ok(Self::Index(U32::read_le(&mut reader)?)),
            1 => Ok(Self::Member(Identifier::read_le(&mut reader)?)),
            2.. => Err(error(format!("Failed to deserialize access variant {variant}"))),
        }
    }
}

impl<N: Network> ToBytes for Access<N> {
    /// Write the access to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()>
    where
        Self: Sized,
    {
        match self {
            Access::Index(index) => {
                u8::write_le(&0u8, &mut writer)?;
                index.write_le(&mut writer)
            }
            Access::Member(identifier) => {
                u8::write_le(&1u8, &mut writer)?;
                identifier.write_le(&mut writer)
            }
        }
    }
}
