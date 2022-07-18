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

impl<N: Network> FromBytes for TransactionLeaf<N> {
    /// Reads the transaction leaf from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the variant.
        let variant = FromBytes::read_le(&mut reader)?;
        // Read the index.
        let index = FromBytes::read_le(&mut reader)?;
        // Read the program ID.
        let program_id = FromBytes::read_le(&mut reader)?;
        // Read the function name.
        let function_name = FromBytes::read_le(&mut reader)?;
        // Read the ID.
        let id = FromBytes::read_le(&mut reader)?;
        // Return the transaction leaf.
        Ok(Self::new(variant, index, program_id, function_name, id))
    }
}

impl<N: Network> ToBytes for TransactionLeaf<N> {
    /// Writes the transaction leaf to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the variant.
        self.variant.write_le(&mut writer)?;
        // Write the index.
        self.index.write_le(&mut writer)?;
        // Write the program ID.
        self.program_id.write_le(&mut writer)?;
        // Write the function name.
        self.function_name.write_le(&mut writer)?;
        // Write the ID.
        self.id.write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: u64 = 1000;

    #[test]
    fn test_bytes() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample the leaf.
            let expected = test_helpers::sample_leaf();

            // Check the byte representation.
            let expected_bytes = expected.to_bytes_le()?;
            assert_eq!(expected, TransactionLeaf::read_le(&expected_bytes[..])?);
            assert!(TransactionLeaf::<CurrentNetwork>::read_le(&expected_bytes[1..]).is_err());
        }
        Ok(())
    }
}
