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

mod parse;

use crate::{Identifier, Plaintext, ValueType};
use snarkvm_console_network::prelude::*;
use snarkvm_utilities::{
    error,
    has_duplicates,
    io::{Read, Result as IoResult, Write},
    FromBytes,
    ToBytes,
};

use itertools::Itertools;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Interface<N: Network> {
    /// The name of the interface.
    name: Identifier<N>,
    /// The name and type for the members of the interface.
    members: Vec<(Identifier<N>, ValueType<N>)>,
}

impl<N: Network> TypeName for Interface<N> {
    /// Returns the type name.
    fn type_name() -> &'static str {
        "interface"
    }
}

impl<N: Network> FromBytes for Interface<N> {
    /// Reads an interface from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the name of the interface.
        let name = Identifier::read_le(&mut reader)?;

        // Read the number of members.
        let num_members = u16::read_le(&mut reader)?;
        // Ensure the number of members is within `N::MAX_DATA_ENTRIES`.
        if num_members as usize > N::MAX_DATA_ENTRIES {
            return Err(error(format!(
                "Interface exceeds size: expected <= {}, found {num_members}",
                N::MAX_DATA_ENTRIES
            )));
        }
        // Read the members.
        let mut members = Vec::with_capacity(num_members as usize);
        for _ in 0..num_members {
            // Read the identifier.
            let identifier = Identifier::read_le(&mut reader)?;
            // Read the value type.
            let value_type = ValueType::read_le(&mut reader)?;
            // Append the member.
            members.push((identifier, value_type));
        }

        // Ensure the members has no duplicate names.
        if has_duplicates(members.iter().map(|(name, ..)| name)) {
            return Err(error(format!("Duplicate member in interface '{name}'")));
        }
        Ok(Self { name, members })
    }
}

impl<N: Network> ToBytes for Interface<N> {
    /// Writes the interface to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Ensure the number of members is within `N::MAX_DATA_ENTRIES`.
        if self.members.len() > N::MAX_DATA_ENTRIES {
            return Err(error("Failed to serialize interface: too many members"));
        }
        // Ensure the members has no duplicate names.
        if has_duplicates(self.members.iter().map(|(name, ..)| name)) {
            return Err(error(format!("Duplicate member in interface '{}'", self.name)));
        }

        // Write the name of the interface.
        self.name.write_le(&mut writer)?;

        // Write the number of members.
        (self.members.len() as u16).write_le(&mut writer)?;
        // Write the members as bytes.
        for (identifier, value_type) in &self.members {
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
        let expected =
            Interface::<CurrentNetwork>::from_str("interface message:\n    first as field;\n    second as field;")?;
        let candidate = Interface::from_bytes_le(&expected.to_bytes_le().unwrap()).unwrap();
        assert_eq!(expected, candidate);
        Ok(())
    }

    #[test]
    fn test_bytes_fails() -> Result<()> {
        let expected = Interface::<CurrentNetwork> {
            name: Identifier::from_str("message")?,
            members: vec![
                (Identifier::from_str("first")?, ValueType::from_str("field")?),
                (Identifier::from_str("first")?, ValueType::from_str("boolean")?),
            ],
        };
        assert!(expected.to_bytes_le().is_err());
        Ok(())
    }
}
