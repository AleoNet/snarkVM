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

impl<N: Network> FromBits for FinalizeOperation<N> {
    /// Reads `Self` from a boolean array in little-endian order.
    fn from_bits_le(bits: &[bool]) -> Result<Self> {
        let mut bits = bits.iter().cloned();

        // Helper function to get the next n bits as a slice.
        let mut next_bits = |n: usize| -> Result<Vec<bool>> {
            let bits: Vec<_> = bits.by_ref().take(n).collect();
            if bits.len() < n {
                bail!("Insufficient bits");
            }
            Ok(bits)
        };

        // Read the variant.
        let variant = u8::from_bits_le(&next_bits(8)?)?;

        // Parse the operation.
        match variant {
            0 => {
                // Read the mapping ID.
                let mapping_id = Field::from_bits_le(&next_bits(Field::<N>::size_in_bits())?)?;
                // Return the finalize operation.
                Ok(Self::InitializeMapping(mapping_id))
            }
            1 => {
                // Read the mapping ID.
                let mapping_id = Field::from_bits_le(&next_bits(Field::<N>::size_in_bits())?)?;
                // Read the key ID.
                let key_id = Field::from_bits_le(&next_bits(Field::<N>::size_in_bits())?)?;
                // Read the value ID.
                let value_id = Field::from_bits_le(&next_bits(Field::<N>::size_in_bits())?)?;
                // Return the finalize operation.
                Ok(Self::InsertKeyValue(mapping_id, key_id, value_id))
            }
            2 => {
                // Read the mapping ID.
                let mapping_id = Field::from_bits_le(&next_bits(Field::<N>::size_in_bits())?)?;
                // Read the index.
                let index = u64::from_bits_le(&next_bits(64)?)?;
                // Read the key ID.
                let key_id = Field::from_bits_le(&next_bits(Field::<N>::size_in_bits())?)?;
                // Read the value ID.
                let value_id = Field::from_bits_le(&next_bits(Field::<N>::size_in_bits())?)?;
                // Return the finalize operation.
                Ok(Self::UpdateKeyValue(mapping_id, index, key_id, value_id))
            }
            3 => {
                // Read the mapping ID.
                let mapping_id = Field::from_bits_le(&next_bits(Field::<N>::size_in_bits())?)?;
                // Read the index.
                let index = u64::from_bits_le(&next_bits(64)?)?;
                // Return the finalize operation.
                Ok(Self::RemoveKeyValue(mapping_id, index))
            }
            4 => {
                // Read the mapping ID.
                let mapping_id = Field::from_bits_le(&next_bits(Field::<N>::size_in_bits())?)?;
                // Return the finalize operation.
                Ok(Self::RemoveMapping(mapping_id))
            }
            5.. => bail!("Invalid finalize operation variant '{variant}'"),
        }
    }

    /// Reads `Self` from a boolean array in big-endian order.
    fn from_bits_be(bits: &[bool]) -> Result<Self> {
        let mut bits = bits.iter().cloned();

        // Helper function to get the next n bits as a slice.
        let mut next_bits = |n: usize| -> Result<Vec<bool>> {
            let bits: Vec<_> = bits.by_ref().take(n).collect();
            if bits.len() < n {
                bail!("Insufficient bits");
            }
            Ok(bits)
        };

        // Read the variant.
        let variant = u8::from_bits_be(&next_bits(8)?)?;

        // Parse the operation.
        match variant {
            0 => {
                // Read the mapping ID.
                let mapping_id = Field::from_bits_be(&next_bits(Field::<N>::size_in_bits())?)?;
                // Return the finalize operation.
                Ok(Self::InitializeMapping(mapping_id))
            }
            1 => {
                // Read the mapping ID.
                let mapping_id = Field::from_bits_be(&next_bits(Field::<N>::size_in_bits())?)?;
                // Read the key ID.
                let key_id = Field::from_bits_be(&next_bits(Field::<N>::size_in_bits())?)?;
                // Read the value ID.
                let value_id = Field::from_bits_be(&next_bits(Field::<N>::size_in_bits())?)?;
                // Return the finalize operation.
                Ok(Self::InsertKeyValue(mapping_id, key_id, value_id))
            }
            2 => {
                // Read the mapping ID.
                let mapping_id = Field::from_bits_be(&next_bits(Field::<N>::size_in_bits())?)?;
                // Read the index.
                let index = u64::from_bits_be(&next_bits(64)?)?;
                // Read the key ID.
                let key_id = Field::from_bits_be(&next_bits(Field::<N>::size_in_bits())?)?;
                // Read the value ID.
                let value_id = Field::from_bits_be(&next_bits(Field::<N>::size_in_bits())?)?;
                // Return the finalize operation.
                Ok(Self::UpdateKeyValue(mapping_id, index, key_id, value_id))
            }
            3 => {
                // Read the mapping ID.
                let mapping_id = Field::from_bits_be(&next_bits(Field::<N>::size_in_bits())?)?;
                // Read the index.
                let index = u64::from_bits_be(&next_bits(64)?)?;
                // Return the finalize operation.
                Ok(Self::RemoveKeyValue(mapping_id, index))
            }
            4 => {
                // Read the mapping ID.
                let mapping_id = Field::from_bits_be(&next_bits(Field::<N>::size_in_bits())?)?;
                // Return the finalize operation.
                Ok(Self::RemoveMapping(mapping_id))
            }
            5.. => bail!("Invalid finalize operation variant '{variant}'"),
        }
    }
}

impl<N: Network> ToBits for FinalizeOperation<N> {
    /// Returns the little-endian bits of the finalize operation.
    fn to_bits_le(&self) -> Vec<bool> {
        match self {
            Self::InitializeMapping(mapping_id) => {
                vec![
                    // Write the variant.
                    0u8.to_bits_le(),
                    // Write the mapping ID.
                    mapping_id.to_bits_le(),
                ]
                .concat()
            }
            Self::InsertKeyValue(mapping_id, key_id, value_id) => {
                vec![
                    // Write the variant.
                    1u8.to_bits_le(),
                    // Write the mapping ID.
                    mapping_id.to_bits_le(),
                    // Write the key ID.
                    key_id.to_bits_le(),
                    // Write the value ID.
                    value_id.to_bits_le(),
                ]
                .concat()
            }
            Self::UpdateKeyValue(mapping_id, index, key_id, value_id) => {
                vec![
                    // Write the variant.
                    2u8.to_bits_le(),
                    // Write the mapping ID.
                    mapping_id.to_bits_le(),
                    // Write the index.
                    index.to_bits_le(),
                    // Write the key ID.
                    key_id.to_bits_le(),
                    // Write the value ID.
                    value_id.to_bits_le(),
                ]
                .concat()
            }
            Self::RemoveKeyValue(mapping_id, index) => {
                vec![
                    // Write the variant.
                    3u8.to_bits_le(),
                    // Write the mapping ID.
                    mapping_id.to_bits_le(),
                    // Write the index.
                    index.to_bits_le(),
                ]
                .concat()
            }
            Self::RemoveMapping(mapping_id) => {
                vec![
                    // Write the variant.
                    4u8.to_bits_le(),
                    // Write the mapping ID.
                    mapping_id.to_bits_le(),
                ]
                .concat()
            }
        }
    }

    /// Returns the big-endian bits of the finalize operation.
    fn to_bits_be(&self) -> Vec<bool> {
        match self {
            Self::InitializeMapping(mapping_id) => {
                vec![
                    // Write the variant.
                    0u8.to_bits_be(),
                    // Write the mapping ID.
                    mapping_id.to_bits_be(),
                ]
                .concat()
            }
            Self::InsertKeyValue(mapping_id, key_id, value_id) => {
                vec![
                    // Write the variant.
                    1u8.to_bits_be(),
                    // Write the mapping ID.
                    mapping_id.to_bits_be(),
                    // Write the key ID.
                    key_id.to_bits_be(),
                    // Write the value ID.
                    value_id.to_bits_be(),
                ]
                .concat()
            }
            Self::UpdateKeyValue(mapping_id, index, key_id, value_id) => {
                vec![
                    // Write the variant.
                    2u8.to_bits_be(),
                    // Write the mapping ID.
                    mapping_id.to_bits_be(),
                    // Write the index.
                    index.to_bits_be(),
                    // Write the key ID.
                    key_id.to_bits_be(),
                    // Write the value ID.
                    value_id.to_bits_be(),
                ]
                .concat()
            }
            Self::RemoveKeyValue(mapping_id, index) => {
                vec![
                    // Write the variant.
                    3u8.to_bits_be(),
                    // Write the mapping ID.
                    mapping_id.to_bits_be(),
                    // Write the index.
                    index.to_bits_be(),
                ]
                .concat()
            }
            Self::RemoveMapping(mapping_id) => {
                vec![
                    // Write the variant.
                    4u8.to_bits_be(),
                    // Write the mapping ID.
                    mapping_id.to_bits_be(),
                ]
                .concat()
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bits_le() {
        for expected in crate::finalize_operation::test_helpers::sample_finalize_operations() {
            // Check the bit representation.
            let expected_bits = expected.to_bits_le();
            assert_eq!(expected, FinalizeOperation::from_bits_le(&expected_bits[..]).unwrap());
        }
    }

    #[test]
    fn test_bits_be() {
        for expected in crate::finalize_operation::test_helpers::sample_finalize_operations() {
            // Check the bit representation.
            let expected_bits = expected.to_bits_be();
            assert_eq!(expected, FinalizeOperation::from_bits_be(&expected_bits[..]).unwrap());
        }
    }
}
