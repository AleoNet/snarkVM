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

#[derive(Clone)]
pub enum Plaintext<A: Aleo> {
    /// A literal.
    Literal(Literal<A>, OnceCell<Vec<Boolean<A>>>),
    /// A composite.
    Composite(Vec<(Identifier<A>, Plaintext<A>)>, OnceCell<Vec<Boolean<A>>>),
}

impl<A: Aleo> Visibility<A> for Plaintext<A> {
    /// Returns the number of field elements to encode `self`.
    fn size_in_fields(&self) -> usize {
        self.to_bits_le().chunks(A::BaseField::size_in_data_bits()).len()
    }
}

impl<A: Aleo> ToFields for Plaintext<A> {
    type Field = Field<A>;

    /// Returns this plaintext as a list of field elements.
    fn to_fields(&self) -> Vec<Self::Field> {
        self.to_bits_le()
            .chunks(A::BaseField::size_in_data_bits())
            .map(|bits_le| Field::from_bits_le(bits_le))
            .collect()
    }
}

impl<A: Aleo> FromFields for Plaintext<A> {
    type Field = Field<A>;

    /// Creates a plaintext from a list of field elements.
    fn from_fields(fields: &[Self::Field]) -> Self {
        Self::from_bits_le(
            &fields
                .iter()
                .map(|field| field.to_bits_le()[..A::BaseField::size_in_data_bits()].to_vec())
                .flatten()
                .collect::<Vec<_>>(),
        )
    }
}

impl<A: Aleo> ToBits for Plaintext<A> {
    type Boolean = Boolean<A>;

    /// Returns this entry as a list of **little-endian** bits.
    fn to_bits_le(&self) -> Vec<Boolean<A>> {
        match self {
            Self::Literal(literal, bits_le) => bits_le
                .get_or_init(|| {
                    let mut bits_le = Vec::new();
                    bits_le.push(Boolean::constant(false));
                    bits_le.extend(literal.variant().to_bits_le());
                    bits_le.extend(literal.size_in_bits().to_bits_le());
                    bits_le.extend(literal.to_bits_le());
                    bits_le
                })
                .clone(),
            Self::Composite(composite, bits_le) => bits_le
                .get_or_init(|| {
                    let mut bits_le = Vec::new();
                    bits_le.push(Boolean::constant(true));
                    bits_le.extend(U8::constant(composite.len() as u8).to_bits_le());
                    for (identifier, value) in composite {
                        let value_bits = value.to_bits_le();
                        bits_le.extend(identifier.size_in_bits().to_bits_le());
                        bits_le.extend(identifier.to_bits_le());
                        bits_le.extend(U16::constant(value_bits.len() as u16).to_bits_le());
                        bits_le.extend(value_bits);
                    }
                    bits_le
                })
                .clone(),
        }
    }

    /// Returns this entry as a list of **big-endian** bits.
    fn to_bits_be(&self) -> Vec<Boolean<A>> {
        match self {
            Self::Literal(literal, bits_be) => bits_be
                .get_or_init(|| {
                    let mut bits_be = Vec::new();
                    bits_be.push(Boolean::constant(false));
                    bits_be.extend(literal.variant().to_bits_be());
                    bits_be.extend(literal.size_in_bits().to_bits_be());
                    bits_be.extend(literal.to_bits_be());
                    bits_be
                })
                .clone(),
            Self::Composite(composite, bits_be) => bits_be
                .get_or_init(|| {
                    let mut bits_be = Vec::new();
                    bits_be.push(Boolean::constant(true));
                    bits_be.extend(U8::constant(composite.len() as u8).to_bits_be());
                    for (identifier, value) in composite {
                        let value_bits = value.to_bits_be();
                        bits_be.extend(identifier.size_in_bits().to_bits_be());
                        bits_be.extend(identifier.to_bits_be());
                        bits_be.extend(U16::constant(value_bits.len() as u16).to_bits_be());
                        bits_be.extend(value_bits);
                    }
                    bits_be
                })
                .clone(),
        }
    }
}

impl<A: Aleo> FromBits for Plaintext<A> {
    type Boolean = Boolean<A>;

    /// Initializes a new value from a list of little-endian bits *without* trailing zeros.
    fn from_bits_le(bits_le: &[Boolean<A>]) -> Self {
        let mut counter = 0;

        let is_literal = !Boolean::from_bits_le(&[bits_le[counter].clone()]).eject_value();
        counter += 1;

        // Literal
        if is_literal {
            let literal_variant = U8::from_bits_le(&bits_le[counter..counter + 8]);
            counter += 8;

            let literal_size = U16::from_bits_le(&bits_le[counter..counter + 16]).eject_value();
            counter += 16;

            let literal = Literal::from_bits_le(&literal_variant, &bits_le[counter..counter + literal_size as usize]);

            // Store the plaintext bits in the cache.
            let cache = OnceCell::new();
            match cache.set(bits_le.to_vec()) {
                // Return the literal.
                Ok(_) => Self::Literal(literal, cache),
                Err(_) => A::halt("Failed to store the plaintext bits in the cache."),
            }
        }
        // Composite
        else {
            let num_composites = U8::from_bits_le(&bits_le[counter..counter + 8]).eject_value();
            counter += 8;

            let mut composites = Vec::with_capacity(num_composites as usize);
            for _ in 0..num_composites {
                let identifier_size = U8::from_bits_le(&bits_le[counter..counter + 8]).eject_value();
                counter += 8;

                let identifier = Identifier::from_bits_le(&bits_le[counter..counter + identifier_size as usize]);
                counter += identifier_size as usize;

                let composite_size = U16::from_bits_le(&bits_le[counter..counter + 16]).eject_value();
                counter += 16;

                let entry = Plaintext::from_bits_le(&bits_le[counter..counter + composite_size as usize]);
                counter += composite_size as usize;

                composites.push((identifier, entry));
            }

            // Store the plaintext bits in the cache.
            let cache = OnceCell::new();
            match cache.set(bits_le.to_vec()) {
                // Return the composite.
                Ok(_) => Self::Composite(composites, cache),
                Err(_) => A::halt("Failed to store the plaintext bits in the cache."),
            }
        }
    }

    /// Initializes a new value from a list of big-endian bits *without* trailing zeros.
    fn from_bits_be(bits_be: &[Boolean<A>]) -> Self {
        let mut counter = 0;

        let is_literal = !Boolean::from_bits_be(&[bits_be[counter].clone()]).eject_value();
        counter += 1;

        // Literal
        if is_literal {
            let literal_variant = U8::from_bits_be(&bits_be[counter..counter + 8]);
            counter += 8;

            let literal_size = U16::from_bits_be(&bits_be[counter..counter + 16]).eject_value();
            counter += 16;

            let literal = Literal::from_bits_be(&literal_variant, &bits_be[counter..counter + literal_size as usize]);
            counter += literal_size as usize;

            // Store the plaintext bits in the cache.
            let cache = OnceCell::new();
            match cache.set(bits_be.to_vec()) {
                // Return the literal.
                Ok(_) => Self::Literal(literal, cache),
                Err(_) => A::halt("Failed to store the plaintext bits in the cache."),
            }
        }
        // Composite
        else {
            let num_composites = U8::from_bits_be(&bits_be[counter..counter + 8]).eject_value();
            counter += 8;

            let mut composites = Vec::with_capacity(num_composites as usize);
            for _ in 0..num_composites {
                let identifier_size = U8::from_bits_be(&bits_be[counter..counter + 8]).eject_value();
                counter += 8;

                let identifier = Identifier::from_bits_be(&bits_be[counter..counter + identifier_size as usize]);
                counter += identifier_size as usize;

                let composite_size = U16::from_bits_be(&bits_be[counter..counter + 16]).eject_value();
                counter += 16;

                let entry = Plaintext::from_bits_be(&bits_be[counter..counter + composite_size as usize]);
                counter += composite_size as usize;

                composites.push((identifier, entry));
            }

            // Store the plaintext bits in the cache.
            let cache = OnceCell::new();
            match cache.set(bits_be.to_vec()) {
                // Return the composite.
                Ok(_) => Self::Composite(composites, cache),
                Err(_) => A::halt("Failed to store the plaintext bits in the cache."),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::AleoV0 as Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    #[test]
    fn test_plaintext() {
        let value = Plaintext::<Circuit>::Literal(Literal::Boolean(Boolean::new(Mode::Private, true)), OnceCell::new());
        assert_eq!(
            value.to_bits_le().eject(),
            Plaintext::<Circuit>::from_bits_le(&value.to_bits_le()).to_bits_le().eject()
        );

        let value = Plaintext::<Circuit>::Literal(
            Literal::Field(Field::new(Mode::Private, UniformRand::rand(&mut test_rng()))),
            OnceCell::new(),
        );
        assert_eq!(
            value.to_bits_le().eject(),
            Plaintext::<Circuit>::from_bits_le(&value.to_bits_le()).to_bits_le().eject()
        );

        let value = Plaintext::<Circuit>::Composite(
            vec![
                (
                    Identifier::new(Mode::Private, "a".into()),
                    Plaintext::<Circuit>::Literal(Literal::Boolean(Boolean::new(Mode::Private, true)), OnceCell::new()),
                ),
                (
                    Identifier::new(Mode::Private, "b".into()),
                    Plaintext::<Circuit>::Literal(
                        Literal::Field(Field::new(Mode::Private, UniformRand::rand(&mut test_rng()))),
                        OnceCell::new(),
                    ),
                ),
            ],
            OnceCell::new(),
        );
        assert_eq!(
            value.to_bits_le().eject(),
            Plaintext::<Circuit>::from_bits_le(&value.to_bits_le()).to_bits_le().eject()
        );

        let value = Plaintext::<Circuit>::Composite(
            vec![
                (
                    Identifier::new(Mode::Private, "a".into()),
                    Plaintext::<Circuit>::Literal(Literal::Boolean(Boolean::new(Mode::Private, true)), OnceCell::new()),
                ),
                (
                    Identifier::new(Mode::Private, "b".into()),
                    Plaintext::<Circuit>::Composite(
                        vec![
                            (
                                Identifier::new(Mode::Private, "c".into()),
                                Plaintext::<Circuit>::Literal(
                                    Literal::Boolean(Boolean::new(Mode::Private, true)),
                                    OnceCell::new(),
                                ),
                            ),
                            (
                                Identifier::new(Mode::Private, "d".into()),
                                Plaintext::<Circuit>::Composite(
                                    vec![
                                        (
                                            Identifier::new(Mode::Private, "e".into()),
                                            Plaintext::<Circuit>::Literal(
                                                Literal::Boolean(Boolean::new(Mode::Private, true)),
                                                OnceCell::new(),
                                            ),
                                        ),
                                        (
                                            Identifier::new(Mode::Private, "f".into()),
                                            Plaintext::<Circuit>::Literal(
                                                Literal::Field(Field::new(
                                                    Mode::Private,
                                                    UniformRand::rand(&mut test_rng()),
                                                )),
                                                OnceCell::new(),
                                            ),
                                        ),
                                    ],
                                    OnceCell::new(),
                                ),
                            ),
                            (
                                Identifier::new(Mode::Private, "g".into()),
                                Plaintext::<Circuit>::Literal(
                                    Literal::Field(Field::new(Mode::Private, UniformRand::rand(&mut test_rng()))),
                                    OnceCell::new(),
                                ),
                            ),
                        ],
                        OnceCell::new(),
                    ),
                ),
                (
                    Identifier::new(Mode::Private, "h".into()),
                    Plaintext::<Circuit>::Literal(
                        Literal::Field(Field::new(Mode::Private, UniformRand::rand(&mut test_rng()))),
                        OnceCell::new(),
                    ),
                ),
            ],
            OnceCell::new(),
        );
        assert_eq!(
            value.to_bits_le().eject(),
            Plaintext::<Circuit>::from_bits_le(&value.to_bits_le()).to_bits_le().eject()
        );
    }
}
