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

use crate::{Ciphertext, Entry, Literal, Plaintext, Visibility};
use snarkvm_circuit_network::Aleo;
use snarkvm_circuit_types::{environment::prelude::*, Boolean, Field, U64};

/// A value stored in program data.
#[derive(Clone)]
pub enum Balance<A: Aleo, Private: Visibility<A>> {
    /// A publicly-visible value.
    Public(U64<A>),
    /// A private value is encrypted under the account owner's address.
    Private(Private),
}

#[cfg(console)]
impl<A: Aleo> Inject for Balance<A, Plaintext<A>> {
    type Primitive = console::Balance<A::Network, console::Plaintext<A::Network>>;

    /// Initializes plaintext balance from a primitive.
    fn new(_: Mode, owner: Self::Primitive) -> Self {
        match owner {
            console::Balance::Public(balance) => Self::Public(U64::new(Mode::Private, balance)),
            console::Balance::Private(console::Plaintext::Literal(console::Literal::U64(balance), ..)) => {
                Self::Private(Plaintext::Literal(Literal::U64(U64::new(Mode::Private, balance)), Default::default()))
            }
            _ => A::halt("Balance::<Plaintext>::new: Invalid primitive type for balance"),
        }
    }
}

#[cfg(console)]
impl<A: Aleo> Inject for Balance<A, Ciphertext<A>> {
    type Primitive = console::Balance<A::Network, console::Ciphertext<A::Network>>;

    /// Initializes ciphertext balance from a primitive.
    fn new(_: Mode, owner: Self::Primitive) -> Self {
        match owner {
            console::Balance::Public(balance) => Self::Public(U64::new(Mode::Private, balance)),
            console::Balance::Private(ciphertext) => Self::Private(Ciphertext::new(Mode::Private, ciphertext)),
        }
    }
}

impl<A: Aleo, Private: Visibility<A>> Balance<A, Private> {
    /// Returns `true` if `self` is public.
    pub fn is_public(&self) -> Boolean<A> {
        Boolean::constant(matches!(self, Self::Public(..)))
    }

    /// Returns `true` if `self` is private.
    pub fn is_private(&self) -> Boolean<A> {
        Boolean::constant(matches!(self, Self::Private(..)))
    }
}

impl<A: Aleo> Balance<A, Plaintext<A>> {
    /// Returns the balance as an `Entry`.
    pub fn to_entry(&self) -> Entry<A, Plaintext<A>> {
        match self {
            Self::Public(balance) => Entry::Public(Plaintext::from(Literal::U64(balance.clone()))),
            Self::Private(plaintext, ..) => Entry::Private(plaintext.clone()),
        }
    }
}

impl<A: Aleo> Deref for Balance<A, Plaintext<A>> {
    type Target = U64<A>;

    /// Returns the balance as a u64.
    fn deref(&self) -> &Self::Target {
        match self {
            Self::Public(public) => public,
            Self::Private(Plaintext::Literal(Literal::U64(balance), ..)) => balance,
            _ => A::halt("Internal error: plaintext deref corrupted in record balance"),
        }
    }
}

impl<A: Aleo> Balance<A, Plaintext<A>> {
    /// Encrypts the balance under the given randomizer.
    pub fn encrypt(&self, randomizer: &[Field<A>]) -> Balance<A, Ciphertext<A>> {
        match self {
            Self::Public(balance) => {
                // Ensure there is exactly zero randomizers.
                if !randomizer.is_empty() {
                    A::halt(format!("Expected 0 randomizers, found {}", randomizer.len()))
                }
                // Ensure the balance is less than or equal to 2^52.
                A::assert(!balance.to_bits_le()[52..].iter().fold(Boolean::constant(false), |acc, bit| acc | bit));
                // Return the balance.
                Balance::Public(balance.clone())
            }
            Self::Private(Plaintext::Literal(Literal::U64(balance), ..)) => {
                // Ensure there is exactly one randomizer.
                if randomizer.len() != 1 {
                    A::halt(format!("Expected 1 randomizer, found {}", randomizer.len()))
                }
                // Ensure the balance is less than or equal to 2^52.
                A::assert(!balance.to_bits_le()[52..].iter().fold(Boolean::constant(false), |acc, bit| acc | bit));
                // Encrypt the balance.
                let ciphertext = balance.to_field() + &randomizer[0];
                // Return the encrypted balance.
                Balance::Private(Ciphertext::from_fields(&[ciphertext]))
            }
            _ => A::halt("Internal error: plaintext encryption corrupted in record balance"),
        }
    }
}

impl<A: Aleo> Balance<A, Ciphertext<A>> {
    /// Decrypts the balance under the given randomizer.
    pub fn decrypt(&self, randomizer: &[Field<A>]) -> Balance<A, Plaintext<A>> {
        match self {
            Self::Public(balance) => {
                // Ensure there is exactly zero randomizers.
                if !randomizer.is_empty() {
                    A::halt(format!("Expected 0 randomizers, found {}", randomizer.len()))
                }
                // Ensure the balance is less than or equal to 2^52.
                A::assert(!balance.to_bits_le()[52..].iter().fold(Boolean::constant(false), |acc, bit| acc | bit));
                // Return the balance.
                Balance::Public(balance.clone())
            }
            Self::Private(ciphertext) => {
                // Ensure there is exactly one randomizer.
                if randomizer.len() != 1 {
                    A::halt(format!("Expected 1 randomizer, found {}", randomizer.len()))
                }
                // Ensure there is exactly one field element in the ciphertext.
                if ciphertext.len() != 1 {
                    A::halt(format!("Expected 1 ciphertext, found {}", ciphertext.len()))
                }
                // Decrypt the balance.
                let balance = U64::from_field(&ciphertext[0] - &randomizer[0]);
                // Ensure the balance is less than or equal to 2^52.
                A::assert(!balance.to_bits_le()[52..].iter().fold(Boolean::constant(false), |acc, bit| acc | bit));
                // Return the balance.
                Balance::Private(Plaintext::from(Literal::U64(balance)))
            }
        }
    }
}

impl<A: Aleo> ToBits for Balance<A, Plaintext<A>> {
    type Boolean = Boolean<A>;

    /// Returns `self` as a boolean vector in little-endian order.
    fn to_bits_le(&self) -> Vec<Boolean<A>> {
        let mut bits_le = vec![self.is_private()];
        match self {
            Self::Public(public) => bits_le.extend(public.to_bits_le()),
            Self::Private(Plaintext::Literal(Literal::U64(balance), ..)) => bits_le.extend(balance.to_bits_le()),
            _ => A::halt("Internal error: plaintext to_bits_le corrupted in record balance"),
        }
        bits_le
    }

    /// Returns `self` as a boolean vector in big-endian order.
    fn to_bits_be(&self) -> Vec<Boolean<A>> {
        let mut bits_be = vec![self.is_private()];
        match self {
            Self::Public(public) => bits_be.extend(public.to_bits_be()),
            Self::Private(Plaintext::Literal(Literal::U64(balance), ..)) => bits_be.extend(balance.to_bits_be()),
            _ => A::halt("Internal error: plaintext to_bits_be corrupted in record balance"),
        }
        bits_be
    }
}

impl<A: Aleo> ToBits for Balance<A, Ciphertext<A>> {
    type Boolean = Boolean<A>;

    /// Returns `self` as a boolean vector in little-endian order.
    fn to_bits_le(&self) -> Vec<Boolean<A>> {
        let mut bits_le = vec![self.is_private()];
        match self {
            Self::Public(public) => bits_le.extend(public.to_bits_le()),
            Self::Private(ciphertext) => {
                // Ensure there is exactly one field element in the ciphertext.
                match ciphertext.len() == 1 {
                    true => bits_le.extend(ciphertext[0].to_bits_le()),
                    false => A::halt("Internal error: ciphertext to_bits_le corrupted in record balance"),
                }
            }
        }
        bits_le
    }

    /// Returns `self` as a boolean vector in big-endian order.
    fn to_bits_be(&self) -> Vec<Boolean<A>> {
        let mut bits_be = vec![self.is_private()];
        match self {
            Self::Public(public) => bits_be.extend(public.to_bits_be()),
            Self::Private(ciphertext) => {
                // Ensure there is exactly one field element in the ciphertext.
                match ciphertext.len() == 1 {
                    true => bits_be.extend(ciphertext[0].to_bits_be()),
                    false => A::halt("Internal error: ciphertext to_bits_be corrupted in record balance"),
                }
            }
        }
        bits_be
    }
}
