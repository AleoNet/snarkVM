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

/// A `ValueType` defines the type parameter for an entry in an `Interface`.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum PlaintextType<N: Network> {
    /// A literal type contains its type name.
    /// The format of the type is `<type_name>`.
    Literal(LiteralType),
    /// An interface type contains its identifier.
    /// The format of the type is `<identifier>`.
    Interface(Identifier<N>),
}

impl<N: Network> PlaintextType<N> {
    /// Returns `true` if the type is a literal.
    /// Returns `false` if the type is an interface.
    pub fn is_literal(&self) -> bool {
        matches!(self, PlaintextType::Literal(..))
    }

    /// Returns `true` if the type is an interface.
    /// Returns `false` if the type is a literal.
    pub fn is_interface(&self) -> bool {
        matches!(self, PlaintextType::Interface(..))
    }
}

impl<N: Network> FromBytes for PlaintextType<N> {
    /// Reads a plaintext type from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let variant = u8::read_le(&mut reader)?;
        match variant {
            0 => Ok(Self::Literal(LiteralType::read_le(&mut reader)?)),
            1 => Ok(Self::Interface(Identifier::read_le(&mut reader)?)),
            2.. => Err(error(format!("Failed to deserialize annotation variant {variant}"))),
        }
    }
}

impl<N: Network> ToBytes for PlaintextType<N> {
    /// Writes a plaintext type to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        match self {
            Self::Literal(literal_type) => {
                u8::write_le(&0u8, &mut writer)?;
                literal_type.write_le(&mut writer)
            }
            Self::Interface(identifier) => {
                u8::write_le(&1u8, &mut writer)?;
                identifier.write_le(&mut writer)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_is_literal() -> Result<()> {
        assert!(PlaintextType::<CurrentNetwork>::Literal(LiteralType::Field).is_literal());
        assert!(!PlaintextType::<CurrentNetwork>::Interface(Identifier::from_str("signature")?).is_literal());
        Ok(())
    }

    #[test]
    fn test_is_interface() -> Result<()> {
        assert!(!PlaintextType::<CurrentNetwork>::Literal(LiteralType::Field).is_interface());
        assert!(PlaintextType::<CurrentNetwork>::Interface(Identifier::from_str("signature")?).is_interface());
        Ok(())
    }
}
