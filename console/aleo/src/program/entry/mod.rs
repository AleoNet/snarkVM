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

use crate::{Address, FromFields, Identifier, Literal, Network, ToFields, ViewKey};
use snarkvm_circuits_environment::Mode;
use snarkvm_curves::{AffineCurve, ProjectiveCurve};
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{FromBits, ToBits};

use anyhow::{bail, Result};
use core::ops::Deref;
use itertools::Itertools;
use once_cell::sync::OnceCell;

pub trait Visibility<N: Network>: ToBits + FromBits + ToFields + FromFields {
    /// Returns the number of field elements to encode `self`.
    fn size_in_fields(&self) -> usize;
}

/// An entry stored in program data.
#[derive(Clone)]
pub enum Entry<N: Network, Private: Visibility<N>> {
    /// A constant entry.
    Constant(Plaintext<N>),
    /// A publicly-visible entry.
    Public(Plaintext<N>),
    /// A private entry encrypted under the account owner's address.
    Private(Private),
}

impl<N: Network> Entry<N, Plaintext<N>> {
    /// Returns the number of field elements to encode `self`.
    pub(crate) fn num_randomizers(&self) -> usize {
        match self {
            // Constant and public entries do not need to be encrypted.
            Self::Constant(..) | Self::Public(..) => 0,
            // Private entries need one randomizer per field element.
            Self::Private(private) => private.size_in_fields(),
        }
    }

    /// Encrypts the entry using the given randomizers.
    pub(crate) fn encrypt(&self, randomizers: &[N::Field]) -> Result<Entry<N, Ciphertext<N>>> {
        // Ensure that the number of randomizers is correct.
        if randomizers.len() != self.num_randomizers() {
            bail!(
                "Failed to encrypt: expected {} randomizers, found {} randomizers",
                randomizers.len(),
                self.num_randomizers()
            )
        }
        match self {
            // Constant entries do not need to be encrypted.
            Self::Constant(plaintext) => Ok(Entry::Constant(plaintext.clone())),
            // Public entries do not need to be encrypted.
            Self::Public(plaintext) => Ok(Entry::Public(plaintext.clone())),
            // Private entries are encrypted with the given randomizers.
            Self::Private(private) => Ok(Entry::Private(Ciphertext(
                private
                    .to_fields()?
                    .iter()
                    .zip_eq(randomizers)
                    .map(|(plaintext, randomizer)| *plaintext + randomizer)
                    .collect(),
            ))),
        }
    }
}

impl<N: Network> Entry<N, Ciphertext<N>> {
    /// Returns the number of field elements to encode `self`.
    pub(crate) fn num_randomizers(&self) -> usize {
        match self {
            // Constant and public entries do not need to be encrypted.
            Self::Constant(..) | Self::Public(..) => 0,
            // Private entries need one randomizer per field element.
            Self::Private(private) => private.size_in_fields(),
        }
    }

    /// Decrypts the entry using the given randomizers.
    pub(crate) fn decrypt(&self, randomizers: &[N::Field]) -> Result<Entry<N, Plaintext<N>>> {
        // Ensure that the number of randomizers is correct.
        if randomizers.len() != self.num_randomizers() {
            bail!(
                "Failed to decrypt: expected {} randomizers, found {} randomizers",
                randomizers.len(),
                self.num_randomizers()
            )
        }
        match self {
            // Constant entries do not need to be decrypted.
            Self::Constant(plaintext) => Ok(Entry::Constant(plaintext.clone())),
            // Public entries do not need to be decrypted.
            Self::Public(plaintext) => Ok(Entry::Public(plaintext.clone())),
            // Private entries are decrypted with the given randomizers.
            Self::Private(private) => Ok(Entry::Private(Plaintext::from_fields(
                &*private
                    .iter()
                    .zip_eq(randomizers)
                    .map(|(ciphertext, randomizer)| *ciphertext - randomizer)
                    .collect::<Vec<_>>(),
            )?)),
        }
    }
}

impl<N: Network, Private: Visibility<N>> ToBits for Entry<N, Private> {
    /// Returns this entry as a list of **little-endian** bits.
    fn to_bits_le(&self) -> Vec<bool> {
        let mut bits_le = match self {
            Self::Constant(..) => vec![false, false],
            Self::Public(..) => vec![false, true],
            Self::Private(..) => vec![true, false],
        };
        match self {
            Self::Constant(entry) => bits_le.extend(entry.to_bits_le()),
            Self::Public(entry) => bits_le.extend(entry.to_bits_le()),
            Self::Private(entry) => bits_le.extend(entry.to_bits_le()),
        }
        bits_le
    }

    /// Returns this entry as a list of **big-endian** bits.
    fn to_bits_be(&self) -> Vec<bool> {
        let mut bits_be = match self {
            Self::Constant(..) => vec![false, false],
            Self::Public(..) => vec![false, true],
            Self::Private(..) => vec![true, false],
        };
        match self {
            Self::Constant(entry) => bits_be.extend(entry.to_bits_be()),
            Self::Public(entry) => bits_be.extend(entry.to_bits_be()),
            Self::Private(entry) => bits_be.extend(entry.to_bits_be()),
        }
        bits_be
    }
}

#[derive(Clone)]
pub enum Plaintext<N: Network> {
    /// A literal.
    Literal(Literal<N>, OnceCell<Vec<bool>>),
    /// A composite.
    Composite(Vec<(Identifier<N>, Plaintext<N>)>, OnceCell<Vec<bool>>),
}

impl<N: Network> Visibility<N> for Plaintext<N> {
    /// Returns the number of field elements to encode `self`.
    fn size_in_fields(&self) -> usize {
        self.to_bits_le().chunks(N::Field::size_in_data_bits()).len()
    }
}

impl<N: Network> ToFields for Plaintext<N> {
    type Field = N::Field;

    /// Returns this plaintext as a list of field elements.
    fn to_fields(&self) -> Result<Vec<Self::Field>> {
        self.to_bits_le().chunks(N::Field::size_in_data_bits()).map(|bits_le| N::field_from_bits_le(bits_le)).collect()
    }
}

impl<N: Network> FromFields for Plaintext<N> {
    type Field = N::Field;

    /// Creates a plaintext from a list of field elements.
    fn from_fields(fields: &[Self::Field]) -> Result<Self> {
        Self::from_bits_le(
            &fields
                .iter()
                .map(|field| field.to_bits_le()[..N::Field::size_in_data_bits()].to_vec())
                .flatten()
                .collect::<Vec<_>>(),
        )
    }
}

impl<N: Network> ToBits for Plaintext<N> {
    /// Returns this entry as a list of **little-endian** bits.
    fn to_bits_le(&self) -> Vec<bool> {
        match self {
            Self::Literal(literal, bits_le) => bits_le
                .get_or_init(|| {
                    let mut bits_le = Vec::new();
                    bits_le.push(false); // Variant bit.
                    bits_le.extend(literal.variant().to_bits_le());
                    bits_le.extend(literal.size_in_bits().to_bits_le());
                    bits_le.extend(literal.to_bits_le());
                    bits_le
                })
                .clone(),
            Self::Composite(composite, bits_le) => bits_le
                .get_or_init(|| {
                    let mut bits_le = Vec::new();
                    bits_le.push(true); // Variant bit.
                    bits_le.extend((composite.len() as u8).to_bits_le());
                    for (identifier, value) in composite {
                        let value_bits = value.to_bits_le();
                        bits_le.extend(identifier.size_in_bits().to_bits_le());
                        bits_le.extend(identifier.to_bits_le());
                        bits_le.extend((value_bits.len() as u16).to_bits_le());
                        bits_le.extend(value_bits);
                    }
                    bits_le
                })
                .clone(),
        }
    }

    /// Returns this entry as a list of **big-endian** bits.
    fn to_bits_be(&self) -> Vec<bool> {
        match self {
            Self::Literal(literal, bits_be) => bits_be
                .get_or_init(|| {
                    let mut bits_be = Vec::new();
                    bits_be.push(false); // Variant bit.
                    bits_be.extend(literal.variant().to_bits_be());
                    bits_be.extend(literal.size_in_bits().to_bits_be());
                    bits_be.extend(literal.to_bits_be());
                    bits_be
                })
                .clone(),
            Self::Composite(composite, bits_be) => bits_be
                .get_or_init(|| {
                    let mut bits_be = Vec::new();
                    bits_be.push(true); // Variant bit.
                    bits_be.extend((composite.len() as u8).to_bits_be());
                    for (identifier, value) in composite {
                        let value_bits = value.to_bits_be();
                        bits_be.extend(identifier.size_in_bits().to_bits_be());
                        bits_be.extend(identifier.to_bits_be());
                        bits_be.extend((value_bits.len() as u16).to_bits_be());
                        bits_be.extend(value_bits);
                    }
                    bits_be
                })
                .clone(),
        }
    }
}

impl<N: Network> FromBits for Plaintext<N> {
    /// Initializes a new value from a list of little-endian bits *without* trailing zeros.
    fn from_bits_le(bits_le: &[bool]) -> Result<Self> {
        let mut counter = 0;

        let is_literal = !bits_le[counter].clone();
        counter += 1;

        // Literal
        if is_literal {
            let literal_variant = u8::from_bits_le(&bits_le[counter..counter + 8])?;
            counter += 8;

            let literal_size = u16::from_bits_le(&bits_le[counter..counter + 16])?;
            counter += 16;

            let literal = Literal::from_bits_le(literal_variant, &bits_le[counter..counter + literal_size as usize])?;

            // Store the plaintext bits in the cache.
            let cache = OnceCell::new();
            match cache.set(bits_le.to_vec()) {
                // Return the literal.
                Ok(_) => Ok(Self::Literal(literal, cache)),
                Err(_) => bail!("Failed to store the plaintext bits in the cache."),
            }
        }
        // Composite
        else {
            let num_composites = u8::from_bits_le(&bits_le[counter..counter + 8])?;
            counter += 8;

            let mut composites = Vec::with_capacity(num_composites as usize);
            for _ in 0..num_composites {
                let identifier_size = u8::from_bits_le(&bits_le[counter..counter + 8])?;
                counter += 8;

                let identifier = Identifier::from_bits_le(&bits_le[counter..counter + identifier_size as usize])?;
                counter += identifier_size as usize;

                let composite_size = u16::from_bits_le(&bits_le[counter..counter + 16])?;
                counter += 16;

                let entry = Plaintext::from_bits_le(&bits_le[counter..counter + composite_size as usize])?;
                counter += composite_size as usize;

                composites.push((identifier, entry));
            }

            // Store the plaintext bits in the cache.
            let cache = OnceCell::new();
            match cache.set(bits_le.to_vec()) {
                // Return the composite.
                Ok(_) => Ok(Self::Composite(composites, cache)),
                Err(_) => bail!("Failed to store the plaintext bits in the cache."),
            }
        }
    }

    /// Initializes a new value from a list of big-endian bits *without* trailing zeros.
    fn from_bits_be(bits_be: &[bool]) -> Result<Self> {
        let mut counter = 0;

        let is_literal = !bits_be[counter].clone();
        counter += 1;

        // Literal
        if is_literal {
            let literal_variant = u8::from_bits_be(&bits_be[counter..counter + 8])?;
            counter += 8;

            let literal_size = u16::from_bits_be(&bits_be[counter..counter + 16])?;
            counter += 16;

            let literal = Literal::from_bits_be(literal_variant, &bits_be[counter..counter + literal_size as usize])?;
            counter += literal_size as usize;

            // Store the plaintext bits in the cache.
            let cache = OnceCell::new();
            match cache.set(bits_be.to_vec()) {
                // Return the literal.
                Ok(_) => Ok(Self::Literal(literal, cache)),
                Err(_) => bail!("Failed to store the plaintext bits in the cache."),
            }
        }
        // Composite
        else {
            let num_composites = u8::from_bits_be(&bits_be[counter..counter + 8])?;
            counter += 8;

            let mut composites = Vec::with_capacity(num_composites as usize);
            for _ in 0..num_composites {
                let identifier_size = u8::from_bits_be(&bits_be[counter..counter + 8])?;
                counter += 8;

                let identifier = Identifier::from_bits_be(&bits_be[counter..counter + identifier_size as usize])?;
                counter += identifier_size as usize;

                let composite_size = u16::from_bits_be(&bits_be[counter..counter + 16])?;
                counter += 16;

                let entry = Plaintext::from_bits_be(&bits_be[counter..counter + composite_size as usize])?;
                counter += composite_size as usize;

                composites.push((identifier, entry));
            }

            // Store the plaintext bits in the cache.
            let cache = OnceCell::new();
            match cache.set(bits_be.to_vec()) {
                // Return the composite.
                Ok(_) => Ok(Self::Composite(composites, cache)),
                Err(_) => bail!("Failed to store the plaintext bits in the cache."),
            }
        }
    }
}

// impl<N: Network, Literal: EntryMode<N>>> Value<N, Literal> {
//     // /// Returns the recursive depth of this entry.
//     // /// Note: Once `generic_const_exprs` is stabilized, this can be replaced with `const DEPTH: u8`.
//     // fn depth(&self, counter: usize) -> usize {
//     //     match self {
//     //         Self::Literal(..) => 1,
//     //         Self::Composite(composite) => {
//     //             // Determine the maximum depth of the composite.
//     //             let max_depth = composite.iter().map(|(_, entry)| entry.depth(counter)).fold(0, |a, b| a.max(b));
//     //             // Add `1` to the depth of the member with the largest depth.
//     //             max_depth.saturating_add(1)
//     //         }
//     //     }
//     // }
// }

#[derive(Clone)]
pub struct Ciphertext<N: Network>(Vec<N::Field>);

impl<N: Network> Visibility<N> for Ciphertext<N> {
    /// Returns the number of field elements to encode `self`.
    fn size_in_fields(&self) -> usize {
        self.0.len()
    }
}

impl<N: Network> ToFields for Ciphertext<N> {
    type Field = N::Field;

    /// Returns this ciphertext as a list of field elements.
    fn to_fields(&self) -> Result<Vec<Self::Field>> {
        Ok(self.0.clone())
    }
}

impl<N: Network> FromFields for Ciphertext<N> {
    type Field = N::Field;

    /// Creates ciphertext from a list of field elements.
    fn from_fields(fields: &[Self::Field]) -> Result<Self> {
        Ok(Ciphertext(fields.to_vec()))
    }
}

impl<N: Network> ToBits for Ciphertext<N> {
    /// Returns this entry as a list of **little-endian** bits.
    fn to_bits_le(&self) -> Vec<bool> {
        let bits_le = self.0.to_bits_le();
        assert_eq!(self.0.len() * N::Field::size_in_bits(), bits_le.len());
        bits_le
    }

    /// Returns this entry as a list of **big-endian** bits.
    fn to_bits_be(&self) -> Vec<bool> {
        let bits_be = self.0.to_bits_be();
        assert_eq!(self.0.len() * N::Field::size_in_bits(), bits_be.len());
        bits_be
    }
}

impl<N: Network> FromBits for Ciphertext<N> {
    /// Returns this entry as a list of **little-endian** bits.
    fn from_bits_le(bits_le: &[bool]) -> Result<Self> {
        Ok(Self(
            bits_le
                .chunks(N::Field::size_in_bits())
                .map(|chunk| N::field_from_bits_le(chunk))
                .collect::<Result<Vec<_>>>()?,
        ))
    }

    /// Returns this entry as a list of **big-endian** bits.
    fn from_bits_be(bits_be: &[bool]) -> Result<Self> {
        Ok(Self(
            bits_be
                .chunks(N::Field::size_in_bits())
                .map(|chunk| N::field_from_bits_be(chunk))
                .collect::<Result<Vec<_>>>()?,
        ))
    }
}

impl<N: Network> Deref for Ciphertext<N> {
    type Target = [N::Field];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Testnet3;
    use snarkvm_utilities::{test_rng, UniformRand};

    use core::str::FromStr;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_plaintext() -> Result<()> {
        let value = Plaintext::<CurrentNetwork>::Literal(Literal::Boolean(true), OnceCell::new());
        assert_eq!(value.to_bits_le(), Plaintext::<CurrentNetwork>::from_bits_le(&value.to_bits_le())?.to_bits_le());

        let value =
            Plaintext::<CurrentNetwork>::Literal(Literal::Field(UniformRand::rand(&mut test_rng())), OnceCell::new());
        assert_eq!(value.to_bits_le(), Plaintext::<CurrentNetwork>::from_bits_le(&value.to_bits_le())?.to_bits_le());

        let value = Plaintext::<CurrentNetwork>::Composite(
            vec![
                (
                    Identifier::from_str("a")?,
                    Plaintext::<CurrentNetwork>::Literal(Literal::Boolean(true), OnceCell::new()),
                ),
                (
                    Identifier::from_str("b")?,
                    Plaintext::<CurrentNetwork>::Literal(
                        Literal::Field(UniformRand::rand(&mut test_rng())),
                        OnceCell::new(),
                    ),
                ),
            ],
            OnceCell::new(),
        );
        assert_eq!(value.to_bits_le(), Plaintext::<CurrentNetwork>::from_bits_le(&value.to_bits_le())?.to_bits_le());

        let value = Plaintext::<CurrentNetwork>::Composite(
            vec![
                (
                    Identifier::from_str("a")?,
                    Plaintext::<CurrentNetwork>::Literal(Literal::Boolean(true), OnceCell::new()),
                ),
                (
                    Identifier::from_str("b")?,
                    Plaintext::<CurrentNetwork>::Composite(
                        vec![
                            (
                                Identifier::from_str("c")?,
                                Plaintext::<CurrentNetwork>::Literal(Literal::Boolean(true), OnceCell::new()),
                            ),
                            (
                                Identifier::from_str("d")?,
                                Plaintext::<CurrentNetwork>::Composite(
                                    vec![
                                        (
                                            Identifier::from_str("e")?,
                                            Plaintext::<CurrentNetwork>::Literal(
                                                Literal::Boolean(true),
                                                OnceCell::new(),
                                            ),
                                        ),
                                        (
                                            Identifier::from_str("f")?,
                                            Plaintext::<CurrentNetwork>::Literal(
                                                Literal::Field(UniformRand::rand(&mut test_rng())),
                                                OnceCell::new(),
                                            ),
                                        ),
                                    ],
                                    OnceCell::new(),
                                ),
                            ),
                            (
                                Identifier::from_str("g")?,
                                Plaintext::<CurrentNetwork>::Literal(
                                    Literal::Field(UniformRand::rand(&mut test_rng())),
                                    OnceCell::new(),
                                ),
                            ),
                        ],
                        OnceCell::new(),
                    ),
                ),
                (
                    Identifier::from_str("h")?,
                    Plaintext::<CurrentNetwork>::Literal(
                        Literal::Field(UniformRand::rand(&mut test_rng())),
                        OnceCell::new(),
                    ),
                ),
            ],
            OnceCell::new(),
        );
        assert_eq!(value.to_bits_le(), Plaintext::<CurrentNetwork>::from_bits_le(&value.to_bits_le())?.to_bits_le());
        Ok(())
    }
}

// pub struct LiteralType<N: Network>(N::Field);
//
// pub trait EntryType {
//     /// Returns the recursive depth of this entry.
//     /// Note: Once `generic_const_exprs` is stabilized, this can be replaced with `const DEPTH: u8`.
//     fn depth(&self, counter: usize) -> usize;
//     /// Returns the identifiers that compose this entry.
//     fn to_identifiers(&self) -> Vec<String>;
//     /// Returns `true` if the entry is a literal.
//     fn is_literal(&self) -> bool;
//     /// Returns `true` if the entry is a composite.
//     fn is_composite(&self) -> bool;
// }
//
// /// An entry stored in program data.
// pub enum Entry<N: Network, Private: EntryType> {
//     /// A constant entry.
//     Constant(Plaintext<N>),
//     /// A publicly-visible entry.
//     Public(Plaintext<N>),
//     /// A private entry encrypted under the account owner's address.
//     Private(Private),
// }
//
// impl<N: Network, Private: EntryType> Entry<N, Private> {
//     /// Returns the recursive depth of this entry.
//     /// Note: Once `generic_const_exprs` is stabilized, this can be replaced with `const DEPTH: u8`.
//     fn depth(&self) -> usize {
//         match self {
//             Self::Constant(constant) => constant.depth(0),
//             Self::Public(public) => public.depth(0),
//             Self::Private(private) => private.depth(0),
//         }
//     }
//
//     /// Returns the identifiers that compose this entry.
//     fn to_identifiers(&self) -> Vec<String> {
//         match self {
//             Self::Constant(constant) => constant.to_identifiers(),
//             Self::Public(public) => public.to_identifiers(),
//             Self::Private(private) => private.to_identifiers(),
//         }
//     }
//
//     // /// If this entry is private, returns the field elements that compose the entry.
//     // /// Otherwise, returns `None`.
//     // fn to_fields(&self) -> Option<Vec<N::Field>> {
//     //     match self {
//     //         Self::Constant(..) => None,
//     //         Self::Public(..) => None,
//     //         Self::Private(private) => Some(private.to_fields()),
//     //     }
//     // }
//
//     /// Returns `true` if the entry is a literal.
//     pub fn is_literal(&self) -> bool {
//         match self {
//             Self::Constant(constant) => constant.is_literal(),
//             Self::Public(public) => public.is_literal(),
//             Self::Private(private) => private.is_literal(),
//         }
//     }
//
//     /// Returns `true` if the entry is a composite.
//     pub fn is_composite(&self) -> bool {
//         match self {
//             Self::Constant(constant) => constant.is_composite(),
//             Self::Public(public) => public.is_composite(),
//             Self::Private(private) => private.is_composite(),
//         }
//     }
//
//     /// Returns the mode of the entry.
//     pub const fn mode(&self) -> Mode {
//         match self {
//             Self::Constant(..) => Mode::Constant,
//             Self::Public(..) => Mode::Public,
//             Self::Private(..) => Mode::Private,
//         }
//     }
//
//     /// Returns `true` if the entry is constant.
//     pub const fn is_constant(&self) -> bool {
//         matches!(self, Self::Constant(..))
//     }
//
//     /// Returns `true` if the entry is public.
//     pub const fn is_public(&self) -> bool {
//         matches!(self, Self::Public(..))
//     }
//
//     /// Returns `true` if the entry is private.
//     pub const fn is_private(&self) -> bool {
//         matches!(self, Self::Private(..))
//     }
// }
//
// pub enum Plaintext<N: Network> {
//     /// A public literal.
//     Literal(Literal<N>),
//     /// A public composite.
//     Composite(Vec<(String, Plaintext<N>)>),
// }
//
// impl<N: Network> EntryType for Plaintext<N> {
//     /// Returns the recursive depth of this public entry.
//     /// Note: Once `generic_const_exprs` is stabilized, this can be replaced with `const DEPTH: u8`.
//     fn depth(&self, counter: usize) -> usize {
//         match self {
//             Self::Literal(..) => 1,
//             Self::Composite(composite) => {
//                 // Determine the maximum depth of the composite.
//                 let max_depth = composite.iter().map(|(_, public)| public.depth(counter)).fold(0, |a, b| a.max(b));
//                 // Add `1` to the depth of the member with the largest depth.
//                 max_depth.saturating_add(1)
//             }
//         }
//     }
//
//     /// Returns the identifiers that compose this public entry.
//     fn to_identifiers(&self) -> Vec<String> {
//         match self {
//             Self::Literal(..) => vec![],
//             Self::Composite(composite) => composite
//                 .iter()
//                 .flat_map(|(identifier, public)| {
//                     // Recursively get the identifiers of the member.
//                     let mut identifiers = vec![identifier.clone()];
//                     identifiers.extend(public.to_identifiers());
//                     identifiers
//                 })
//                 .collect(),
//         }
//     }
//
//     /// Returns `true` if the entry is a literal.
//     fn is_literal(&self) -> bool {
//         matches!(self, Self::Literal(..))
//     }
//
//     /// Returns `true` if the entry is a composite.
//     fn is_composite(&self) -> bool {
//         matches!(self, Self::Composite(..))
//     }
// }
//
// pub enum Ciphertext<N: Network> {
//     /// A private literal.
//     Literal(LiteralType<N>, Vec<N::Field>),
//     /// A private composite.
//     Composite(Vec<(String, Ciphertext<N>)>),
// }
//
// impl<N: Network> EntryType for Ciphertext<N> {
//     /// Returns the recursive depth of this private entry.
//     /// Note: Once `generic_const_exprs` is stabilized, this can be replaced with `const DEPTH: u8`.
//     fn depth(&self, counter: usize) -> usize {
//         match self {
//             Self::Literal(..) => 1,
//             Self::Composite(composite) => {
//                 // Determine the maximum depth of the composite.
//                 let max_depth = composite.iter().map(|(_, private)| private.depth(counter)).fold(0, |a, b| a.max(b));
//                 // Add `1` to the depth of the member with the largest depth.
//                 max_depth.saturating_add(1)
//             }
//         }
//     }
//
//     /// Returns the identifiers that compose this private entry.
//     fn to_identifiers(&self) -> Vec<String> {
//         match self {
//             Self::Literal(..) => vec![],
//             Self::Composite(composite) => composite
//                 .iter()
//                 .flat_map(|(identifier, private)| {
//                     // Recursively get the identifiers of the member.
//                     let mut identifiers = vec![identifier.clone()];
//                     identifiers.extend(private.to_identifiers());
//                     identifiers
//                 })
//                 .collect(),
//         }
//     }
//
//     /// Returns `true` if the entry is a literal.
//     fn is_literal(&self) -> bool {
//         matches!(self, Self::Literal(..))
//     }
//
//     /// Returns `true` if the entry is a composite.
//     fn is_composite(&self) -> bool {
//         matches!(self, Self::Composite(..))
//     }
// }
//
// impl<N: Network> Ciphertext<N> {
//     /// Returns the field elements that compose this private entry.
//     fn to_fields(&self) -> Vec<N::Field> {
//         match self {
//             Self::Literal(_, literal) => (*literal).clone(),
//             Self::Composite(composite) => composite.iter().flat_map(|(_, private)| private.to_fields()).collect(),
//         }
//     }
//
//     /// Returns the number of field elements required to represent this private entry.
//     fn len(&self) -> usize {
//         match self {
//             Self::Literal(_, literal) => literal.len(),
//             Self::Composite(composite) => composite.iter().map(|(_, private)| private.len()).sum(),
//         }
//     }
// }
