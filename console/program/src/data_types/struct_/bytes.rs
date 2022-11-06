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

impl<N: Network> FromBytes for Struct<N> {
    /// Reads a struct from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the name of the struct.
        let name = Identifier::read_le(&mut reader)?;

        // Read the number of members.
        let num_members = u16::read_le(&mut reader)?;
        // Ensure the number of members is within `N::MAX_DATA_ENTRIES`.
        if num_members as usize > N::MAX_DATA_ENTRIES {
            return Err(error(format!(
                "Struct exceeds size: expected <= {}, found {num_members}",
                N::MAX_DATA_ENTRIES
            )));
        }
        // Read the members.
        let mut members = IndexMap::with_capacity(num_members as usize);
        for _ in 0..num_members {
            // Read the identifier.
            let identifier = Identifier::read_le(&mut reader)?;
            // Read the plaintext type.
            let plaintext_type = PlaintextType::read_le(&mut reader)?;
            // Insert the member, and ensure the member has no duplicate names.
            if members.insert(identifier, plaintext_type).is_some() {
                return Err(error(format!("Duplicate identifier in struct '{name}'")));
            };
        }

        Ok(Self { name, members })
    }
}

impl<N: Network> ToBytes for Struct<N> {
    /// Writes the struct to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Ensure the number of members is within `N::MAX_DATA_ENTRIES`.
        if self.members.len() > N::MAX_DATA_ENTRIES {
            return Err(error("Failed to serialize struct: too many members"));
        }

        // Write the name of the struct.
        self.name.write_le(&mut writer)?;

        // Write the number of members.
        u16::try_from(self.members.len()).or_halt_with::<N>("Struct length exceeds u16").write_le(&mut writer)?;
        // Write the members as bytes.
        for (identifier, plaintext_type) in &self.members {
            // Write the identifier.
            identifier.write_le(&mut writer)?;
            // Write the plaintext type to the buffer.
            plaintext_type.write_le(&mut writer)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_bytes() -> Result<()> {
        let expected =
            Struct::<CurrentNetwork>::from_str("struct message:\n    first as field;\n    second as field;")?;
        let candidate = Struct::from_bytes_le(&expected.to_bytes_le().unwrap()).unwrap();
        assert_eq!(expected, candidate);
        Ok(())
    }
}
