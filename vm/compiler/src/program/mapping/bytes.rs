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

impl<N: Network> FromBytes for Mapping<N> {
    /// Reads the mapping from a buffer.
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the mapping name.
        let name = Identifier::<N>::read_le(&mut reader)?;
        // Read the key statement.
        let key = FromBytes::read_le(&mut reader)?;
        // Read the value statement.
        let value = FromBytes::read_le(&mut reader)?;
        // Return the new mapping.
        Ok(Self::new(name, key, value))
    }
}

impl<N: Network> ToBytes for Mapping<N> {
    /// Writes the mapping to a buffer.
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the mapping name.
        self.name.write_le(&mut writer)?;
        // Write the key statement.
        self.key.write_le(&mut writer)?;
        // Write the value statement.
        self.value.write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_mapping_bytes() -> Result<()> {
        let mapping_string = r"
mapping main:
    key a as field.public;
    value b as field.public;";

        let expected = Mapping::<CurrentNetwork>::from_str(mapping_string)?;
        let expected_bytes = expected.to_bytes_le()?;
        println!("String size: {:?}, Bytecode size: {:?}", mapping_string.as_bytes().len(), expected_bytes.len());

        let candidate = Mapping::<CurrentNetwork>::from_bytes_le(&expected_bytes)?;
        assert_eq!(expected.to_string(), candidate.to_string());
        assert_eq!(expected_bytes, candidate.to_bytes_le()?);
        Ok(())
    }
}
