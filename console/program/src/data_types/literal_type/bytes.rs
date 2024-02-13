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

impl<N: Network> FromBytes for LiteralType<N> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let index = u8::read_le(&mut reader)?;
        match index {
            0 => Ok(LiteralType::Address),
            1 => Ok(LiteralType::Boolean),
            2 => {
                // Read the length of the data.
                let length = U32::read_le(&mut reader)?;
                // Check that the length of the data is valid.
                if length.is_zero() {
                    Err(error("Data literal must have a non-zero length".to_string()))
                } else if *length > N::MAX_DATA_SIZE_IN_FIELDS {
                    Err(error(format!("Data literal exceeds the maximum length of {}.", N::MAX_DATA_SIZE_IN_FIELDS)))
                } else {
                    Ok(LiteralType::Data(U32::read_le(&mut reader)?))
                }
            }
            3 => Ok(LiteralType::Field),
            4 => Ok(LiteralType::Group),
            5 => Ok(LiteralType::I8),
            6 => Ok(LiteralType::I16),
            7 => Ok(LiteralType::I32),
            8 => Ok(LiteralType::I64),
            9 => Ok(LiteralType::I128),
            10 => Ok(LiteralType::U8),
            11 => Ok(LiteralType::U16),
            12 => Ok(LiteralType::U32),
            13 => Ok(LiteralType::U64),
            14 => Ok(LiteralType::U128),
            15 => Ok(LiteralType::Scalar),
            16 => Ok(LiteralType::Signature),
            17 => Ok(LiteralType::String),
            _ => Err(error("Failed to deserialize literal type variant {index}")),
        }
    }
}

impl<N: Network> ToBytes for LiteralType<N> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        match self {
            LiteralType::Address
            | LiteralType::Boolean
            | LiteralType::Field
            | LiteralType::Group
            | LiteralType::I8
            | LiteralType::I16
            | LiteralType::I32
            | LiteralType::I64
            | LiteralType::I128
            | LiteralType::U8
            | LiteralType::U16
            | LiteralType::U32
            | LiteralType::U64
            | LiteralType::U128
            | LiteralType::Scalar
            | LiteralType::Signature
            | LiteralType::String => self.type_id().write_le(&mut writer),
            LiteralType::Data(length) => {
                self.type_id().write_le(&mut writer)?;
                length.write_le(&mut writer)
            }
        }
    }
}
