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
use snarkvm_console_types::{Field, U64};

/// A value stored in program data.
#[derive(Clone, PartialEq, Eq)]
pub enum Balance<N: Network, Private: Visibility> {
    /// A publicly-visible value.
    Public(U64<N>),
    /// A private value is encrypted under the account owner's address.
    Private(Private),
}

impl<N: Network, Private: Visibility> Balance<N, Private> {
    /// Returns `true` if `self` is public.
    pub const fn is_public(&self) -> bool {
        matches!(self, Self::Public(..))
    }

    /// Returns `true` if `self` is private.
    pub const fn is_private(&self) -> bool {
        matches!(self, Self::Private(..))
    }
}

impl<N: Network> Balance<N, Plaintext<N>> {
    /// Returns the balance as an `Entry`.
    pub fn to_entry(&self) -> Entry<N, Plaintext<N>> {
        match self {
            Self::Public(balance) => Entry::Public(Plaintext::from(Literal::U64(*balance))),
            Self::Private(plaintext, ..) => Entry::Private(plaintext.clone()),
        }
    }
}

impl<N: Network> Deref for Balance<N, Plaintext<N>> {
    type Target = U64<N>;

    /// Returns the balance as a u64.
    fn deref(&self) -> &Self::Target {
        match self {
            Self::Public(public) => public,
            Self::Private(Plaintext::Literal(Literal::U64(balance), ..)) => balance,
            _ => N::halt("Internal error: plaintext deref corrupted in record balance"),
        }
    }
}

impl<N: Network> Balance<N, Plaintext<N>> {
    /// Encrypts the balance under the given randomizer.
    pub fn encrypt(&self, randomizer: &[Field<N>]) -> Result<Balance<N, Ciphertext<N>>> {
        match self {
            Self::Public(balance) => {
                // Ensure there is exactly zero randomizers.
                ensure!(randomizer.is_empty(), "Expected 0 randomizers, found {}", randomizer.len());
                // Ensure the balance is less than or equal to 2^52.
                ensure!(balance.to_bits_le()[52..].iter().all(|bit| !bit), "Attempted to encrypt an invalid balance");
                // Return the balance.
                Ok(Balance::Public(*balance))
            }
            Self::Private(Plaintext::Literal(Literal::U64(balance), ..)) => {
                // Ensure there is exactly one randomizer.
                ensure!(randomizer.len() == 1, "Expected 1 randomizer, found {}", randomizer.len());
                // Ensure the balance is less than or equal to 2^52.
                ensure!(balance.to_bits_le()[52..].iter().all(|bit| !bit), "Attempted to encrypt an invalid balance");
                // Encrypt the balance.
                let ciphertext = balance.to_field()? + randomizer[0];
                // Return the encrypted balance.
                Ok(Balance::Private(Ciphertext::from_fields(&[ciphertext])?))
            }
            _ => bail!("Internal error: plaintext encryption corrupted in record balance"),
        }
    }
}

impl<N: Network> Balance<N, Ciphertext<N>> {
    /// Decrypts the balance under the given randomizer.
    pub fn decrypt(&self, randomizer: &[Field<N>]) -> Result<Balance<N, Plaintext<N>>> {
        match self {
            Self::Public(balance) => {
                // Ensure there is exactly zero randomizers.
                ensure!(randomizer.is_empty(), "Expected 0 randomizers, found {}", randomizer.len());
                // Ensure the balance is less than or equal to 2^52.
                ensure!(balance.to_bits_le()[52..].iter().all(|bit| !bit), "Attempted to decrypt an invalid balance");
                // Return the balance.
                Ok(Balance::Public(*balance))
            }
            Self::Private(ciphertext) => {
                // Ensure there is exactly one randomizer.
                ensure!(randomizer.len() == 1, "Expected 1 randomizer, found {}", randomizer.len());
                // Ensure there is exactly one field element in the ciphertext.
                ensure!(ciphertext.len() == 1, "Expected 1 ciphertext, found {}", ciphertext.len());
                // Decrypt the balance.
                let balance = U64::from_field(&(ciphertext[0] - randomizer[0]))?;
                // Ensure the balance is less than or equal to 2^52.
                ensure!(balance.to_bits_le()[52..].iter().all(|bit| !bit), "Attempted to decrypt an invalid balance");
                // Return the balance.
                Ok(Balance::Private(Plaintext::from(Literal::U64(balance))))
            }
        }
    }
}

impl<N: Network> ToBits for Balance<N, Plaintext<N>> {
    /// Returns `self` as a boolean vector in little-endian order.
    fn to_bits_le(&self) -> Vec<bool> {
        let mut bits_le = vec![self.is_private()];
        match self {
            Self::Public(public) => bits_le.extend(public.to_bits_le()),
            Self::Private(Plaintext::Literal(Literal::U64(balance), ..)) => bits_le.extend(balance.to_bits_le()),
            _ => N::halt("Internal error: plaintext to_bits_le corrupted in record balance"),
        }
        bits_le
    }

    /// Returns `self` as a boolean vector in big-endian order.
    fn to_bits_be(&self) -> Vec<bool> {
        let mut bits_be = vec![self.is_private()];
        match self {
            Self::Public(public) => bits_be.extend(public.to_bits_be()),
            Self::Private(Plaintext::Literal(Literal::U64(balance), ..)) => bits_be.extend(balance.to_bits_be()),
            _ => N::halt("Internal error: plaintext to_bits_be corrupted in record balance"),
        }
        bits_be
    }
}

impl<N: Network> ToBits for Balance<N, Ciphertext<N>> {
    /// Returns `self` as a boolean vector in little-endian order.
    fn to_bits_le(&self) -> Vec<bool> {
        let mut bits_le = vec![self.is_private()];
        match self {
            Self::Public(public) => bits_le.extend(public.to_bits_le()),
            Self::Private(ciphertext) => {
                // Ensure there is exactly one field element in the ciphertext.
                match ciphertext.len() == 1 {
                    true => bits_le.extend(ciphertext[0].to_bits_le()),
                    false => N::halt("Internal error: ciphertext to_bits_le corrupted in record balance"),
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
                    false => N::halt("Internal error: ciphertext to_bits_be corrupted in record balance"),
                }
            }
        }
        bits_be
    }
}

impl<N: Network> Debug for Balance<N, Plaintext<N>> {
    /// Prints the balance as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Balance<N, Plaintext<N>> {
    /// Prints the balance as a string, i.e. `42u64.public`.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Self::Public(balance) => write!(f, "{balance}.public"),
            Self::Private(Plaintext::Literal(Literal::U64(balance), ..)) => write!(f, "{balance}.private"),
            _ => N::halt("Internal error: plaintext fmt corrupted in record balance"),
        }
    }
}

impl<N: Network, Private: Visibility> FromBytes for Balance<N, Private> {
    /// Reads the balance from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the index.
        let index = u8::read_le(&mut reader)?;
        // Read the balance.
        let balance = match index {
            0 => Self::Public(U64::read_le(&mut reader)?),
            1 => Self::Private(Private::read_le(&mut reader)?),
            2.. => return Err(error(format!("Failed to decode balance variant {index}"))),
        };
        Ok(balance)
    }
}

impl<N: Network, Private: Visibility> ToBytes for Balance<N, Private> {
    /// Writes the balance to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        match self {
            Self::Public(balance) => {
                0u8.write_le(&mut writer)?;
                balance.write_le(&mut writer)
            }
            Self::Private(balance) => {
                1u8.write_le(&mut writer)?;
                balance.write_le(&mut writer)
            }
        }
    }
}
