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

impl<N: Network, Private: Visibility> FromBytes for Record<N, Private> {
    /// Reads the record from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the owner.
        let owner = Owner::read_le(&mut reader)?;
        // Read the gates.
        let gates = Balance::read_le(&mut reader)?;
        // Read the number of entries in the record data.
        let num_entries = u16::read_le(&mut reader)?;
        // Read the record data.
        let mut data = IndexMap::with_capacity(num_entries as usize);
        for _ in 0..num_entries {
            // Read the identifier.
            let identifier = Identifier::<N>::read_le(&mut reader)?;
            // Read the entry value (in 2 steps to prevent infinite recursion).
            let num_bytes = u16::read_le(&mut reader)?;
            // Read the entry bytes.
            let bytes = (0..num_bytes).map(|_| u8::read_le(&mut reader)).collect::<Result<Vec<_>, _>>()?;
            // Recover the entry value.
            let entry = Entry::read_le(&mut bytes.as_slice())?;
            // Add the entry.
            data.insert(identifier, entry);
        }

        // Prepare the reserved entry names.
        let reserved = [
            Identifier::from_str("owner").map_err(|e| error(e.to_string()))?,
            Identifier::from_str("gates").map_err(|e| error(e.to_string()))?,
        ];
        // Ensure the entries has no duplicate names.
        if has_duplicates(data.iter().map(|(identifier, _)| identifier).chain(reserved.iter())) {
            return Err(error("Duplicate entry type found in record"));
        }
        // Ensure the number of entries is within `N::MAX_DATA_ENTRIES`.
        if data.len() > N::MAX_DATA_ENTRIES {
            return Err(error("Failed to parse record: too many entries"));
        }

        Ok(Self { owner, gates, data })
    }
}

impl<N: Network, Private: Visibility> ToBytes for Record<N, Private> {
    /// Writes the record to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the owner.
        self.owner.write_le(&mut writer)?;
        // Write the gates.
        self.gates.write_le(&mut writer)?;
        // Write the number of entries in the record data.
        (self.data.len() as u16).write_le(&mut writer)?;
        // Write each entry.
        for (entry_name, entry_value) in &self.data {
            // Write the entry name.
            entry_name.write_le(&mut writer)?;
            // Write the entry value (performed in 2 steps to prevent infinite recursion).
            let bytes = entry_value.to_bytes_le().map_err(|e| error(e.to_string()))?;
            // Write the number of bytes.
            (bytes.len() as u16).write_le(&mut writer)?;
            // Write the bytes.
            bytes.write_le(&mut writer)?;
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
        // Construct a new record.
        let expected = Record::<CurrentNetwork, Plaintext<CurrentNetwork>>::from_str(
            "{ owner: aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.private, gates: 5u64.private, token_amount: 100u64.private }",
        )?;

        // Check the byte representation.
        let expected_bytes = expected.to_bytes_le()?;
        assert_eq!(expected, Record::read_le(&expected_bytes[..])?);
        assert!(Record::<CurrentNetwork, Plaintext<CurrentNetwork>>::read_le(&expected_bytes[1..]).is_err());
        Ok(())
    }
}
