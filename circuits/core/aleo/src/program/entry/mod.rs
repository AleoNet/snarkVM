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

use crate::{Aleo, Identifier, Literal};
use snarkvm_circuits_types::{environment::prelude::*, Boolean, Field, U16, U8};
use snarkvm_curves::{AffineCurve, ProjectiveCurve};

pub trait Visibility<A: Aleo>: ToBits<Boolean = Boolean<A>> {
    fn from_bits_le(bits_le: &[Boolean<A>]) -> Self;
}

/// An entry stored in program data.
pub enum Entry<A: Aleo, Private: Visibility<A>> {
    /// A constant entry.
    Constant(Plaintext<A>),
    /// A publicly-visible entry.
    Public(Plaintext<A>),
    /// A private entry encrypted under the account owner's address.
    Private(Private),
}

impl<A: Aleo, Private: Visibility<A>> ToBits for Entry<A, Private> {
    type Boolean = Boolean<A>;

    /// Returns this entry as a list of **little-endian** bits.
    fn to_bits_le(&self) -> Vec<Self::Boolean> {
        match self {
            Entry::Constant(entry) => entry.to_bits_le(),
            Entry::Public(entry) => entry.to_bits_le(),
            Entry::Private(entry) => entry.to_bits_le(),
        }
    }

    /// Returns this entry as a list of **big-endian** bits.
    fn to_bits_be(&self) -> Vec<Self::Boolean> {
        match self {
            Entry::Constant(entry) => entry.to_bits_be(),
            Entry::Public(entry) => entry.to_bits_be(),
            Entry::Private(entry) => entry.to_bits_be(),
        }
    }
}

// impl<A: Aleo> Value<A, Plaintext<A>> {
//     fn size_in_fields(&self) -> usize {
//         self.to_bits_le().chunks(A::BaseField::size_in_data_bits()).len()
//     }
//
//     fn encrypt(&self, randomizers: &[Field<A>]) -> Value<A, Ciphertext<A>> {
//         let ciphertext = self.to_bits_le()
//             .chunks(A::BaseField::size_in_data_bits())
//             .map(|bits_le| Field::from_bits_le(bits_le))
//             .into_iter()
//             .zip_eq(randomizers.iter())
//             .map(|(plaintext, randomizer)| plaintext + randomizer)
//             .collect();
//
//
//     }
// }

pub enum Plaintext<A: Aleo> {
    /// A literal.
    Literal(Literal<A>),
    /// A composite.
    Composite(Vec<(Identifier<A>, Plaintext<A>)>),
}

impl<A: Aleo> Visibility<A> for Plaintext<A> {
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
            counter += literal_size as usize;

            Self::Literal(literal)
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

            Self::Composite(composites)
        }
    }
}

impl<A: Aleo> ToBits for Plaintext<A> {
    type Boolean = Boolean<A>;

    /// Returns this entry as a list of **little-endian** bits.
    fn to_bits_le(&self) -> Vec<Boolean<A>> {
        match self {
            Self::Literal(literal) => {
                let mut bits_le = Vec::new();
                bits_le.push(Boolean::constant(false));
                bits_le.extend(literal.variant().to_bits_le());
                bits_le.extend(literal.size_in_bits().to_bits_le());
                bits_le.extend(literal.to_bits_le());
                bits_le
            }
            Self::Composite(composite) => {
                let mut bits_le = Vec::new();
                bits_le.push(Boolean::constant(true));
                bits_le.extend(U8::constant(composite.len() as u8).to_bits_le());
                for (identifier, value) in composite {
                    let mut value_bits = value.to_bits_le();
                    bits_le.extend(identifier.size_in_bits().to_bits_le());
                    bits_le.extend(identifier.to_bits_le());
                    bits_le.extend(U16::constant(value_bits.len() as u16).to_bits_le());
                    bits_le.extend(value_bits);
                }
                bits_le
            }
        }
    }

    /// Returns this entry as a list of **big-endian** bits.
    fn to_bits_be(&self) -> Vec<Boolean<A>> {
        match self {
            Self::Literal(literal) => {
                let mut bits_be = Vec::new();
                bits_be.push(Boolean::constant(false));
                bits_be.extend(literal.variant().to_bits_be());
                bits_be.extend(literal.size_in_bits().to_bits_be());
                bits_be.extend(literal.to_bits_be());
                bits_be
            }
            Self::Composite(composite) => {
                let mut bits_be = Vec::new();
                bits_be.push(Boolean::constant(true));
                bits_be.extend(U8::constant(composite.len() as u8).to_bits_be());
                for (identifier, value) in composite {
                    let mut value_bits = value.to_bits_be();
                    bits_be.extend(identifier.size_in_bits().to_bits_be());
                    bits_be.extend(identifier.to_bits_be());
                    bits_be.extend(U16::constant(value_bits.len() as u16).to_bits_be());
                    bits_be.extend(value_bits);
                }
                bits_be
            }
        }
    }
}

// impl<A: Aleo, Literal: EntryMode<A>> Value<A, Literal> {
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

// pub struct Plaintext<A: Aleo>(Literal<A>);

// impl<A: Aleo> Plaintext<A> {
//     /// Returns the number of field elements required to represent this plaintext.
//     fn size_in_fields(&self) -> usize {
//         // self.0.
//     }
//
//     fn encrypt(&self, randomizers: &[Field<A>]) -> Ciphertext<A> {
//
//     }
// }

// impl<A: Aleo> ToBits for Plaintext<A> {
//     type Boolean = Boolean<A>;
//
//     /// Returns this entry as a list of **little-endian** bits.
//     fn to_bits_le(&self) -> Vec<Self::Boolean> {
//         self.0.to_bits_le()
//     }
//
//     /// Returns this entry as a list of **big-endian** bits.
//     fn to_bits_be(&self) -> Vec<Self::Boolean> {
//         self.0.to_bits_be()
//     }
// }

pub struct Ciphertext<A: Aleo>(Vec<Field<A>>);

impl<A: Aleo> Visibility<A> for Ciphertext<A> {
    fn from_bits_le(bits_le: &[Boolean<A>]) -> Self {
        Self(bits_le.chunks(A::BaseField::size_in_bits()).map(|chunk| Field::from_bits_le(chunk)).collect())
    }
}

impl<A: Aleo> ToBits for Ciphertext<A> {
    type Boolean = Boolean<A>;

    /// Returns this entry as a list of **little-endian** bits.
    fn to_bits_le(&self) -> Vec<Self::Boolean> {
        let bits_le = self.0.to_bits_le();
        assert_eq!(self.0.len() * A::BaseField::size_in_bits(), bits_le.len());
        bits_le
    }

    /// Returns this entry as a list of **big-endian** bits.
    fn to_bits_be(&self) -> Vec<Self::Boolean> {
        let bits_be = self.0.to_bits_be();
        assert_eq!(self.0.len() * A::BaseField::size_in_bits(), bits_be.len());
        bits_be
    }
}

// impl<A: Aleo> Ciphertext<A> {
//     /// Returns the field elements that compose this entry.
//     fn to_fields(&self) -> Vec<Field<A>> {
//         match self {
//             Self::Literal(_, literal) => (*literal).clone(),
//             Self::Composite(composite) => composite.iter().flat_map(|(_, private)| private.to_fields()).collect(),
//         }
//     }
//
//     /// Returns the number of field elements required to represent this entry.
//     fn len(&self) -> usize {
//         match self {
//             Self::Literal(_, literal) => literal.len(),
//             Self::Composite(composite) => composite.iter().map(|(_, private)| private.len()).sum(),
//         }
//     }
// }

#[cfg(test)]
mod tests {
    use super::*;
    use crate::AleoV0 as Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    #[test]
    fn test_value() {
        let value = Plaintext::<Circuit>::Literal(Literal::Boolean(Boolean::new(Mode::Private, true)));
        assert_eq!(
            value.to_bits_le().eject(),
            Plaintext::<Circuit>::from_bits_le(&value.to_bits_le()).to_bits_le().eject()
        );

        let value = Plaintext::<Circuit>::Literal(Literal::Field(Field::new(
            Mode::Private,
            UniformRand::rand(&mut test_rng()),
        )));
        assert_eq!(
            value.to_bits_le().eject(),
            Plaintext::<Circuit>::from_bits_le(&value.to_bits_le()).to_bits_le().eject()
        );

        let value = Plaintext::<Circuit>::Composite(vec![
            (
                Identifier::new(Mode::Private, "a".into()),
                Plaintext::<Circuit>::Literal(Literal::Boolean(Boolean::new(Mode::Private, true))),
            ),
            (
                Identifier::new(Mode::Private, "b".into()),
                Plaintext::<Circuit>::Literal(Literal::Field(Field::new(
                    Mode::Private,
                    UniformRand::rand(&mut test_rng()),
                ))),
            ),
        ]);
        assert_eq!(
            value.to_bits_le().eject(),
            Plaintext::<Circuit>::from_bits_le(&value.to_bits_le()).to_bits_le().eject()
        );

        let value = Plaintext::<Circuit>::Composite(vec![
            (
                Identifier::new(Mode::Private, "a".into()),
                Plaintext::<Circuit>::Literal(Literal::Boolean(Boolean::new(Mode::Private, true))),
            ),
            (
                Identifier::new(Mode::Private, "b".into()),
                Plaintext::<Circuit>::Composite(vec![
                    (
                        Identifier::new(Mode::Private, "c".into()),
                        Plaintext::<Circuit>::Literal(Literal::Boolean(Boolean::new(Mode::Private, true))),
                    ),
                    (
                        Identifier::new(Mode::Private, "d".into()),
                        Plaintext::<Circuit>::Composite(vec![
                            (
                                Identifier::new(Mode::Private, "e".into()),
                                Plaintext::<Circuit>::Literal(Literal::Boolean(Boolean::new(Mode::Private, true))),
                            ),
                            (
                                Identifier::new(Mode::Private, "f".into()),
                                Plaintext::<Circuit>::Literal(Literal::Field(Field::new(
                                    Mode::Private,
                                    UniformRand::rand(&mut test_rng()),
                                ))),
                            ),
                        ]),
                    ),
                    (
                        Identifier::new(Mode::Private, "g".into()),
                        Plaintext::<Circuit>::Literal(Literal::Field(Field::new(
                            Mode::Private,
                            UniformRand::rand(&mut test_rng()),
                        ))),
                    ),
                ]),
            ),
            (
                Identifier::new(Mode::Private, "h".into()),
                Plaintext::<Circuit>::Literal(Literal::Field(Field::new(
                    Mode::Private,
                    UniformRand::rand(&mut test_rng()),
                ))),
            ),
        ]);
        assert_eq!(
            value.to_bits_le().eject(),
            Plaintext::<Circuit>::from_bits_le(&value.to_bits_le()).to_bits_le().eject()
        );
    }
}
