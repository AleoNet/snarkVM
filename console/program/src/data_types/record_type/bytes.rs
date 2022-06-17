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

impl<N: Network> FromBytes for RecordType<N> {
    /// Reads a record type from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the name of the record type.
        let name = Identifier::read_le(&mut reader)?;
        // Read the visibility for the owner.
        let owner = PublicOrPrivate::read_le(&mut reader)?;
        // Read the visibility for the balance.
        let balance = PublicOrPrivate::read_le(&mut reader)?;

        // Read the number of entries.
        let num_entries = u16::read_le(&mut reader)?;
        // Ensure the number of entries is within `N::MAX_DATA_ENTRIES`.
        if num_entries as usize > N::MAX_DATA_ENTRIES {
            return Err(error(format!(
                "RecordType exceeds size: expected <= {}, found {num_entries}",
                N::MAX_DATA_ENTRIES
            )));
        }
        // Read the entries.
        let mut entries = IndexMap::with_capacity(num_entries as usize);
        for _ in 0..num_entries {
            // Read the identifier.
            let identifier = Identifier::read_le(&mut reader)?;
            // Read the entry type.
            let entry = EntryType::read_le(&mut reader)?;
            // Insert the entry, and ensure the entries has no duplicate names.
            if entries.insert(identifier, entry).is_some() {
                return Err(error(format!("Duplicate identifier in record '{name}'")));
            };
        }

        Ok(Self { name, owner, balance, entries })
    }
}

impl<N: Network> ToBytes for RecordType<N> {
    /// Writes the record type to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Ensure the number of entries is within `N::MAX_DATA_ENTRIES`.
        if self.entries.len() > N::MAX_DATA_ENTRIES {
            return Err(error("Failed to serialize record: too many entries"));
        }

        // Write the name of the record type.
        self.name.write_le(&mut writer)?;
        // Write the visibility for the owner.
        self.owner.write_le(&mut writer)?;
        // Write the visibility for the balance.
        self.balance.write_le(&mut writer)?;

        // Write the number of entries.
        (self.entries.len() as u16).write_le(&mut writer)?;
        // Write the entries as bytes.
        for (identifier, value_type) in &self.entries {
            // Write the identifier.
            identifier.write_le(&mut writer)?;
            // Write the value type to the buffer.
            value_type.write_le(&mut writer)?;
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
        let expected = RecordType::<CurrentNetwork>::from_str(
            "record message:\n    owner as address.public;\n    balance as u64.private;\n    first as field.constant;\n    second as field.public;",
        )?;
        let candidate = RecordType::from_bytes_le(&expected.to_bytes_le().unwrap()).unwrap();
        assert_eq!(expected, candidate);
        Ok(())
    }
}
