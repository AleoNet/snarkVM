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
use crate::{Identifier, LiteralType};

impl<N: Network> FromBytes for ArrayType<N> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the innermost element type.
        let variant = u8::read_le(&mut reader)?;
        let element_type = match variant {
            0 => PlaintextType::Literal(LiteralType::read_le(&mut reader)?),
            1 => PlaintextType::Struct(Identifier::read_le(&mut reader)?),
            2.. => return Err(error(format!("Failed to deserialize element type {variant}"))),
        };

        // Read the number of dimensions of the array.
        let dimensions = u8::read_le(&mut reader)? as usize;

        // Ensure the dimensions of the array are valid.
        match dimensions {
            0 => return Err(error("Array type must have at least one dimension.")),
            dimensions if dimensions < N::MAX_DATA_DEPTH => (),
            _ => return Err(error(format!("Array type exceeds the maximum depth of {}.", N::MAX_DATA_DEPTH))),
        }

        // Read the lengths of the array.
        let mut lengths = Vec::with_capacity(dimensions);
        for _ in 0..dimensions {
            lengths.push(U32::read_le(&mut reader)?);
        }

        // Construct the array type.
        ArrayType::new(element_type, lengths).map_err(|e| error(format!("{e}")))
    }
}

impl<N: Network> ToBytes for ArrayType<N> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Initialize storage
        let mut element_type = *self.element_type.clone();
        let mut lengths = vec![*self.length()];

        // Collect the each dimension of the array.
        // Note that the lengths are in the order of the outermost dimension to the innermost dimension.
        for _ in 1..N::MAX_DATA_DEPTH {
            element_type = match element_type {
                PlaintextType::Literal(_) | PlaintextType::Struct(_) => break,
                PlaintextType::Array(array_type) => {
                    lengths.push(*array_type.length());
                    array_type.element_type().clone()
                }
            };
        }

        // Check that the array type does not exceed the maximum depth.
        if let PlaintextType::Array(_) = element_type {
            return Err(error(format!("Array type exceeds the maximum depth of {}.", N::MAX_DATA_DEPTH)));
        }

        // Write the innermost element type.
        match element_type {
            PlaintextType::Literal(literal_type) => {
                0u8.write_le(&mut writer)?;
                literal_type.write_le(&mut writer)?;
            }
            PlaintextType::Struct(identifier) => {
                1u8.write_le(&mut writer)?;
                identifier.write_le(&mut writer)?;
            }
            PlaintextType::Array(_) => unreachable!(),
        }

        // Write the number of dimensions of the array.
        u8::try_from(lengths.len()).or_halt::<N>().write_le(&mut writer)?;

        // Write the lengths of the array.
        for length in lengths {
            length.write_le(&mut writer)?;
        }

        Ok(())
    }
}
