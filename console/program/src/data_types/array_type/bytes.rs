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

impl<N: Network> FromBytes for ArrayType<N> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let variant = u8::read_le(&mut reader)?;
        match variant {
            0 => Ok(Self::new_literal(LiteralType::read_le(&mut reader)?, U32::read_le(&mut reader)?).map_err(error)?),
            1 => Ok(Self::new_struct(Identifier::read_le(&mut reader)?, U32::read_le(&mut reader)?).map_err(error)?),
            2.. => Err(error(format!("Failed to deserialize annotation variant {variant}"))),
        }
    }
}

impl<N: Network> ToBytes for ArrayType<N> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        match self {
            Self::Literal(literal_type, length) => {
                0u8.write_le(&mut writer)?;
                literal_type.write_le(&mut writer)?;
                length.write_le(&mut writer)
            }
            Self::Struct(identifier, length) => {
                1u8.write_le(&mut writer)?;
                identifier.write_le(&mut writer)?;
                length.write_le(&mut writer)
            }
        }
    }
}
