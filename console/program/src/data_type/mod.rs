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

mod entry;
pub use entry::Entry;

mod interface;
pub use interface::Interface;

mod literal_type;
pub use literal_type::LiteralType;

mod value_type;
pub use value_type::ValueType;

use crate::Identifier;
use snarkvm_console_network::prelude::*;

mod parse;

use snarkvm_utilities::{
    error,
    has_duplicates,
    io::{Read, Result as IoResult, Write},
    FromBytes,
    ToBytes,
};

/// The declared layout for program data.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct DataType<N: Network> {
    /// The name of the data type.
    name: Identifier<N>,
    /// The name and type for the entries in data.
    entries: Vec<(Identifier<N>, Entry<N>)>,
}

impl<N: Network> TypeName for DataType<N> {
    /// Returns the type name.
    fn type_name() -> &'static str {
        "record"
    }
}

impl<N: Network> TryFrom<(Identifier<N>, Vec<(Identifier<N>, Entry<N>)>)> for DataType<N> {
    type Error = Error;

    /// Initializes a new `DataType` from a vector of `(Identifier, Entry)` pairs.
    fn try_from((name, entries): (Identifier<N>, Vec<(Identifier<N>, Entry<N>)>)) -> Result<Self> {
        // Ensure the number of entries is within `N::MAX_DATA_ENTRIES`.
        match entries.len() <= N::MAX_DATA_ENTRIES {
            true => Ok(Self { name, entries }),
            false => bail!("Data exceeds size: expected <= {}, found {}", N::MAX_DATA_ENTRIES, entries.len()),
        }
    }
}

impl<N: Network> FromBytes for DataType<N> {
    /// Reads a data type from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the name of the data type.
        let name = Identifier::read_le(&mut reader)?;

        // Read the number of entries.
        let num_entries = u16::read_le(&mut reader)?;
        // Ensure the number of entries is within `N::MAX_DATA_ENTRIES`.
        if num_entries as usize > N::MAX_DATA_ENTRIES {
            return Err(error(format!(
                "DataType exceeds size: expected <= {}, found {num_entries}",
                N::MAX_DATA_ENTRIES
            )));
        }
        // Read the entries.
        let mut entries = Vec::with_capacity(num_entries as usize);
        for _ in 0..num_entries {
            // Read the identifier.
            let identifier = Identifier::read_le(&mut reader)?;
            // Read the entry.
            let entry = Entry::read_le(&mut reader)?;
            // Append the entry.
            entries.push((identifier, entry));
        }

        // Ensure the entries has no duplicate names.
        if has_duplicates(entries.iter().map(|(name, ..)| name)) {
            return Err(error(format!("Duplicate entry in record '{name}'")));
        }
        Ok(Self { name, entries })
    }
}

impl<N: Network> ToBytes for DataType<N> {
    /// Writes the data type to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Ensure the number of entries is within `N::MAX_DATA_ENTRIES`.
        if self.entries.len() > N::MAX_DATA_ENTRIES {
            return Err(error("Failed to serialize record: too many entries"));
        }
        // Ensure the entries has no duplicate names.
        if has_duplicates(self.entries.iter().map(|(name, ..)| name)) {
            return Err(error(format!("Duplicate entry in record '{}'", self.name)));
        }

        // Write the name of the data type.
        self.name.write_le(&mut writer)?;

        // Write the number of entries.
        (self.entries.len() as u16).write_le(&mut writer)?;
        // Write the entries as bytes.
        for (identifier, entry) in &self.entries {
            // Write the identifier.
            identifier.write_le(&mut writer)?;
            // Write the entry to the buffer.
            entry.write_le(&mut writer)?;
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
        let expected = DataType::<CurrentNetwork>::from_str(
            "record message:\n    first as field.constant;\n    second as field.public;",
        )?;
        let candidate = DataType::from_bytes_le(&expected.to_bytes_le().unwrap()).unwrap();
        assert_eq!(expected, candidate);
        Ok(())
    }

    #[test]
    fn test_bytes_fails() -> Result<()> {
        let expected = DataType::<CurrentNetwork> {
            name: Identifier::from_str("message")?,
            entries: vec![
                (Identifier::from_str("first")?, Entry::from_str("field.public")?),
                (Identifier::from_str("first")?, Entry::from_str("boolean.private")?),
            ],
        };
        assert!(expected.to_bytes_le().is_err());
        Ok(())
    }
}
