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

use crate::{Ciphertext, Entry, Literal, Plaintext};
use snarkvm_console_network::prelude::*;
use snarkvm_console_types::{Address, Field};

/// A value stored in program data.
#[derive(Clone, PartialEq, Eq)]
pub enum Owner<N: Network, Private: Visibility> {
    /// A publicly-visible value.
    Public(Address<N>),
    /// A private value is encrypted under the account owner's address.
    Private(Private),
}

impl<N: Network, Private: Visibility> Owner<N, Private> {
    /// Returns `true` if `self` is public.
    pub const fn is_public(&self) -> bool {
        matches!(self, Self::Public(..))
    }

    /// Returns `true` if `self` is private.
    pub const fn is_private(&self) -> bool {
        matches!(self, Self::Private(..))
    }
}

impl<N: Network> Owner<N, Plaintext<N>> {
    /// Returns the owner as an `Entry`.
    pub fn to_entry(&self) -> Entry<N, Plaintext<N>> {
        match self {
            Self::Public(owner) => Entry::Public(Plaintext::from(Literal::Address(*owner))),
            Self::Private(plaintext, ..) => Entry::Private(plaintext.clone()),
        }
    }
}

impl<N: Network> Deref for Owner<N, Plaintext<N>> {
    type Target = Address<N>;

    /// Returns the address of the owner.
    fn deref(&self) -> &Self::Target {
        match self {
            Self::Public(public) => public,
            Self::Private(Plaintext::Literal(Literal::Address(address), ..)) => address,
            _ => N::halt("Internal error: plaintext deref corrupted in record owner"),
        }
    }
}

impl<N: Network> Owner<N, Plaintext<N>> {
    /// Encrypts `self` under the given randomizer.
    pub fn encrypt(&self, randomizer: &[Field<N>]) -> Result<Owner<N, Ciphertext<N>>> {
        match self {
            Self::Public(public) => {
                // Ensure there is exactly zero randomizers.
                ensure!(randomizer.is_empty(), "Expected 0 randomizers, found {}", randomizer.len());
                // Return the owner.
                Ok(Owner::Public(*public))
            }
            Self::Private(Plaintext::Literal(Literal::Address(address), ..)) => {
                // Ensure there is exactly one randomizer.
                ensure!(randomizer.len() == 1, "Expected 1 randomizer, found {}", randomizer.len());
                // Encrypt the owner.
                let ciphertext = address.to_field()? + randomizer[0];
                // Return the encrypted owner.
                Ok(Owner::Private(Ciphertext::from_fields(&[ciphertext])?))
            }
            _ => bail!("Internal error: plaintext encryption corrupted in record owner"),
        }
    }
}

impl<N: Network> Owner<N, Ciphertext<N>> {
    /// Decrypts the owner under the given randomizer.
    pub fn decrypt(&self, randomizer: &[Field<N>]) -> Result<Owner<N, Plaintext<N>>> {
        match self {
            Self::Public(public) => {
                // Ensure there is exactly zero randomizers.
                ensure!(randomizer.is_empty(), "Expected 0 randomizers, found {}", randomizer.len());
                // Return the owner.
                Ok(Owner::Public(*public))
            }
            Self::Private(ciphertext) => {
                // Ensure there is exactly one randomizer.
                ensure!(randomizer.len() == 1, "Expected 1 randomizer, found {}", randomizer.len());
                // Ensure there is exactly one field element in the ciphertext.
                ensure!(ciphertext.len() == 1, "Expected 1 ciphertext, found {}", ciphertext.len());
                // Decrypt the owner.
                let owner = Address::from_field(&(ciphertext[0] - randomizer[0]))?;
                // Return the owner.
                Ok(Owner::Private(Plaintext::from(Literal::Address(owner))))
            }
        }
    }
}

impl<N: Network> ToBits for Owner<N, Plaintext<N>> {
    /// Returns `self` as a boolean vector in little-endian order.
    fn to_bits_le(&self) -> Vec<bool> {
        let mut bits_le = vec![self.is_private()];
        match self {
            Self::Public(public) => bits_le.extend(public.to_bits_le()),
            Self::Private(Plaintext::Literal(Literal::Address(address), ..)) => bits_le.extend(address.to_bits_le()),
            _ => N::halt("Internal error: plaintext to_bits_le corrupted in record owner"),
        }
        bits_le
    }

    /// Returns `self` as a boolean vector in big-endian order.
    fn to_bits_be(&self) -> Vec<bool> {
        let mut bits_be = vec![self.is_private()];
        match self {
            Self::Public(public) => bits_be.extend(public.to_bits_be()),
            Self::Private(Plaintext::Literal(Literal::Address(address), ..)) => bits_be.extend(address.to_bits_be()),
            _ => N::halt("Internal error: plaintext to_bits_be corrupted in record owner"),
        }
        bits_be
    }
}

impl<N: Network> ToBits for Owner<N, Ciphertext<N>> {
    /// Returns `self` as a boolean vector in little-endian order.
    fn to_bits_le(&self) -> Vec<bool> {
        let mut bits_le = vec![self.is_private()];
        match self {
            Self::Public(public) => bits_le.extend(public.to_bits_le()),
            Self::Private(ciphertext) => {
                // Ensure there is exactly one field element in the ciphertext.
                match ciphertext.len() == 1 {
                    true => bits_le.extend(ciphertext[0].to_bits_le()),
                    false => N::halt("Internal error: ciphertext to_bits_le corrupted in record owner"),
                }
            }
        }
        bits_le
    }

    /// Returns `self` as a boolean vector in big-endian order.
    fn to_bits_be(&self) -> Vec<bool> {
        let mut bits_be = vec![self.is_private()];
        match self {
            Self::Public(public) => bits_be.extend(public.to_bits_be()),
            Self::Private(ciphertext) => {
                // Ensure there is exactly one field element in the ciphertext.
                match ciphertext.len() == 1 {
                    true => bits_be.extend(ciphertext[0].to_bits_be()),
                    false => N::halt("Internal error: ciphertext to_bits_be corrupted in record owner"),
                }
            }
        }
        bits_be
    }
}

impl<N: Network> Debug for Owner<N, Plaintext<N>> {
    /// Prints the owner as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Owner<N, Plaintext<N>> {
    /// Prints the owner as a string, i.e. `aleo1xxx.public`.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Self::Public(owner) => write!(f, "{owner}.public"),
            Self::Private(Plaintext::Literal(Literal::Address(owner), ..)) => write!(f, "{owner}.private"),
            _ => N::halt("Internal error: plaintext fmt corrupted in record owner"),
        }
    }
}

impl<N: Network, Private: Visibility> FromBytes for Owner<N, Private> {
    /// Reads the owner from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the index.
        let index = u8::read_le(&mut reader)?;
        // Read the owner.
        let owner = match index {
            0 => Self::Public(Address::read_le(&mut reader)?),
            1 => Self::Private(Private::read_le(&mut reader)?),
            2.. => return Err(error(format!("Failed to decode owner variant {index}"))),
        };
        Ok(owner)
    }
}

impl<N: Network, Private: Visibility> ToBytes for Owner<N, Private> {
    /// Writes the owner to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        match self {
            Self::Public(owner) => {
                0u8.write_le(&mut writer)?;
                owner.write_le(&mut writer)
            }
            Self::Private(owner) => {
                1u8.write_le(&mut writer)?;
                owner.write_le(&mut writer)
            }
        }
    }
}
