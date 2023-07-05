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
        // Read the innermost element type.
        let variant = u8::read_le(&mut reader)?;
        let element_type = match variant {
            0 => PlaintextType::Literal(LiteralType::read_le(&mut reader)?),
            1 => PlaintextType::Struct(Identifier::read_le(&mut reader)?),
            2.. => return Err(error(format!("Invalid variant {variant} for the innermost element type"))),
        };
        // Read the number of dimensions of the array.
        let num_dimensions = match u8::read_le(&mut reader) {
            Ok(num_dimensions) if (0 < num_dimensions) && (num_dimensions as usize <= N::MAX_DATA_DEPTH) => {
                num_dimensions
            }
            _ => return Err(error(format!("Invalid number of dimensions")))?,
        };
        // Read the lengths of the array.
        let mut lengths = Vec::with_capacity(num_dimensions as usize);
        for _ in 0..num_dimensions {
            lengths.push(u32::read_le(&mut reader)?);
        }
        // Construct an iterator over the lengths.
        let mut lengths = lengths.iter().rev();
        // Get the last length and construct the array type.
        // Note that this unwrap is safe since we have already checked that `num_dimensions` is greater than zero.
        let mut array_type = ArrayType::new(element_type.clone(), U32::new(*lengths.next().unwrap()))
            .map_err(|e| error(format!("{}", e)))?;
        // Construct the array type from the remaining lengths.
        for length in lengths {
            array_type = ArrayType::new(PlaintextType::Array(array_type), U32::new(*length))
                .map_err(|e| error(format!("{}", e)))?;
        }
        Ok(array_type)
    }
}

impl<N: Network> ToBytes for ArrayType<N> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Get the lengths and the innermost element type.
        let mut lengths = Vec::with_capacity(N::MAX_DATA_DEPTH);
        lengths.push(self.length());
        let mut element_type = self.element_type();
        for _ in 1..N::MAX_DATA_DEPTH {
            match element_type {
                PlaintextType::Array(array_type) => {
                    lengths.push(array_type.length());
                    element_type = array_type.element_type();
                }
                _ => break,
            }
        }
        // Write the element type. If the element type is not a literal or a struct, then return an error.
        match element_type {
            PlaintextType::Literal(literal_type) => {
                u8::write_le(&0u8, &mut writer)?;
                literal_type.write_le(&mut writer)?;
            }
            PlaintextType::Struct(identifier) => {
                u8::write_le(&1u8, &mut writer)?;
                identifier.write_le(&mut writer)?;
            }
            _ => return Err(error(format!("Invalid element type"))),
        };
        // Write the number of dimensions.
        u8::write_le(&(lengths.len() as u8), &mut writer)?;
        // Write the lengths in reverse order.
        for length in lengths.iter().rev() {
            u32::write_le(length, &mut writer)?;
        }
        Ok(())
    }
}
