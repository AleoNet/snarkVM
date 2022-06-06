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

use crate::{Identifier, LiteralType};
use snarkvm_console_network::prelude::*;
use snarkvm_utilities::{
    error,
    io::{Read, Result as IoResult, Write},
    FromBytes,
    ToBytes,
};

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Interface<N: Network> {
    /// A literal.
    Literal(LiteralType),
    /// A composite.
    Composite(Vec<(Identifier<N>, Interface<N>)>),
}

impl<N: Network> FromBytes for Interface<N> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let variant = u8::read_le(&mut reader)?;
        match variant {
            0 => Ok(Self::Literal(FromBytes::read_le(&mut reader)?)),
            1 => {
                // Read the number of composites.
                let num_composites = u16::read_le(&mut reader)?;
                // Ensure the number of composites is within `N::MAX_DATA_ENTRIES`.
                if num_composites as usize > N::MAX_DATA_ENTRIES {
                    return Err(error(format!(
                        "Interface exceeds size: expected <= {}, found {num_composites}",
                        N::MAX_DATA_ENTRIES
                    )));
                }
                // Read the composites.
                let mut composites = Vec::with_capacity(num_composites as usize);
                for _ in 0..num_composites {
                    // Read the identifier.
                    let identifier = Identifier::read_le(&mut reader)?;
                    // Read the number of bytes for the composite.
                    let num_bytes = read_variable_length_integer(&mut reader)?;
                    // Read the composite.
                    let mut bytes = vec![0; num_bytes as usize];
                    reader.read_exact(&mut bytes)?;
                    // Append the composite.
                    composites.push((identifier, Interface::read_le(&mut bytes.as_slice())?));
                }
                Ok(Self::Composite(composites))
            }
            2.. => Err(error(format!("Failed to deserialize interface variant {variant}"))),
        }
    }
}

impl<N: Network> ToBytes for Interface<N> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        match self {
            Self::Literal(literal) => {
                u8::write_le(&0u8, &mut writer)?;
                literal.write_le(&mut writer)
            }
            Self::Composite(composite) => {
                // Ensure the composite is within `P::MAX_DATA_ENTRIES`.
                if composite.len() > N::MAX_DATA_ENTRIES {
                    return Err(error("Failed to serialize interface: too many entries"));
                }

                // Write the variant.
                u8::write_le(&1u8, &mut writer)?;
                // Write the number of composite members.
                (composite.len() as u16).write_le(&mut writer)?;
                // Write the composite as bytes.
                for (identifier, interface) in composite {
                    // Write the identifier.
                    identifier.write_le(&mut writer)?;
                    // Attempt to serialize the interface.
                    match interface.to_bytes_le() {
                        Ok(bytes) => {
                            // Write the size in bytes of the interface.
                            variable_length_integer(&(bytes.len() as u64)).write_le(&mut writer)?;
                            // Write the interface to the buffer.
                            bytes.write_le(&mut writer)?;
                        }
                        Err(err) => return Err(error(format!("{err}"))),
                    }
                }
                Ok(())
            }
        }
    }
}
