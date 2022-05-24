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

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Plaintext<N: Network> {
    /// A literal.
    Literal(Literal<N>, OnceCell<Vec<bool>>),
    /// A composite.
    Composite(Vec<(Identifier<N>, Plaintext<N>)>, OnceCell<Vec<bool>>),
}

impl<N: Network> From<Literal<N>> for Plaintext<N> {
    /// Returns a new `Plaintext` from a `Literal`.
    fn from(literal: Literal<N>) -> Self {
        Self::Literal(literal, OnceCell::new())
    }
}

impl<N: Network> From<&Literal<N>> for Plaintext<N> {
    /// Returns a new `Plaintext` from a `Literal`.
    fn from(literal: &Literal<N>) -> Self {
        Self::Literal(literal.clone(), OnceCell::new())
    }
}

impl<N: Network> Visibility<N> for Plaintext<N> {
    /// Returns the number of field elements to encode `self`.
    fn size_in_fields(&self) -> Result<u16> {
        // Compute the number of bits.
        let num_bits = self.to_bits_le().len() + 1; // 1 extra bit for the terminus indicator.
        // Compute the ceiling division of the number of bits by the number of bits in a field element.
        let num_fields = (num_bits + N::Field::size_in_data_bits() - 1) / N::Field::size_in_data_bits();
        match num_fields < N::MAX_DATA_SIZE_IN_FIELDS as usize {
            // Return the number of field elements.
            true => Ok(num_fields as u16),
            false => bail!("Plaintext is too large to encode in field elements."),
        }
    }
}

impl<N: Network> ToFields for Plaintext<N> {
    type Field = N::Field;

    /// Returns this plaintext as a list of field elements.
    fn to_fields(&self) -> Result<Vec<Self::Field>> {
        // Encode the data as little-endian bits.
        let mut bits_le = self.to_bits_le();
        // Adds one final bit to the data, to serve as a terminus indicator.
        // During decryption, this final bit ensures we've reached the end.
        bits_le.push(true);
        // Pack the bits into field elements.
        bits_le.chunks(N::Field::size_in_data_bits()).map(|bits_le| N::field_from_bits_le(bits_le)).collect()
    }
}

impl<N: Network> FromFields for Plaintext<N> {
    type Field = N::Field;

    /// Creates a plaintext from a list of field elements.
    fn from_fields(fields: &[Self::Field]) -> Result<Self> {
        // Unpack the field elements into little-endian bits, and reverse the list for popping the terminus bit off.
        let mut bits_le =
            fields.iter().flat_map(|field| field.to_bits_le()[..N::Field::size_in_data_bits()].to_vec()).rev();
        // Remove the terminus bit that was added during encoding.
        for boolean in bits_le.by_ref() {
            // Drop all extraneous `0` bits, in addition to the final `1` bit.
            if boolean {
                // This case will always be reached, since the terminus bit is always `1`.
                break;
            }
        }
        // Reverse the bits back and recover the data from the bits.
        Self::from_bits_le(&bits_le.rev().collect::<Vec<_>>())
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
