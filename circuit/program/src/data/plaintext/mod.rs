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

mod encrypt;
mod find;
mod from_bits;
mod from_fields;
mod num_randomizers;
mod size_in_fields;
mod to_bits;
mod to_fields;

use crate::{Ciphertext, Identifier, Literal, Visibility};
use snarkvm_circuit_network::Aleo;
use snarkvm_circuit_types::{environment::prelude::*, Address, Boolean, Field, Scalar, U16, U8};

#[derive(Clone)]
pub enum Plaintext<A: Aleo> {
    /// A plaintext literal.
    Literal(Literal<A>, OnceCell<Vec<Boolean<A>>>),
    /// A plaintext interface.
    Interface(IndexMap<Identifier<A>, Plaintext<A>>, OnceCell<Vec<Boolean<A>>>),
}

#[cfg(console)]
impl<A: Aleo> Inject for Plaintext<A> {
    type Primitive = console::Plaintext<A::Network>;

    /// Initializes a new plaintext circuit from a primitive.
    fn new(mode: Mode, plaintext: Self::Primitive) -> Self {
        match plaintext {
            Self::Primitive::Literal(literal, _) => Self::Literal(Literal::new(mode, literal), Default::default()),
            Self::Primitive::Interface(interface, _) => {
                Self::Interface(Inject::new(mode, interface), Default::default())
            }
        }
    }
}

#[cfg(console)]
impl<A: Aleo> Eject for Plaintext<A> {
    type Primitive = console::Plaintext<A::Network>;

    /// Ejects the mode of the plaintext value.
    fn eject_mode(&self) -> Mode {
        match self {
            Self::Literal(literal, _) => literal.eject_mode(),
            Self::Interface(interface, _) => interface
                .iter()
                .map(|(identifier, value)| (identifier, value).eject_mode())
                .collect::<Vec<_>>()
                .eject_mode(),
        }
    }

    /// Ejects the plaintext value.
    fn eject_value(&self) -> Self::Primitive {
        match self {
            Self::Literal(literal, _) => console::Plaintext::Literal(literal.eject_value(), Default::default()),
            Self::Interface(interface, _) => console::Plaintext::Interface(
                interface.iter().map(|pair| pair.eject_value()).collect(),
                Default::default(),
            ),
        }
    }
}

impl<A: Aleo> From<Literal<A>> for Plaintext<A> {
    /// Returns a new `Plaintext` from a `Literal`.
    fn from(literal: Literal<A>) -> Self {
        Self::Literal(literal, OnceCell::new())
    }
}

impl<A: Aleo> From<&Literal<A>> for Plaintext<A> {
    /// Returns a new `Plaintext` from a `Literal`.
    fn from(literal: &Literal<A>) -> Self {
        Self::Literal((*literal).clone(), OnceCell::new())
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::{test_rng, Uniform};

    use anyhow::Result;

    #[test]
    fn test_plaintext() -> Result<()> {
        let value = Plaintext::<Circuit>::Literal(Literal::Boolean(Boolean::new(Mode::Private, true)), OnceCell::new());
        assert_eq!(
            value.to_bits_le().eject(),
            Plaintext::<Circuit>::from_bits_le(&value.to_bits_le()).to_bits_le().eject()
        );

        let value = Plaintext::<Circuit>::Literal(
            Literal::Field(Field::new(Mode::Private, Uniform::rand(&mut test_rng()))),
            OnceCell::new(),
        );
        assert_eq!(
            value.to_bits_le().eject(),
            Plaintext::<Circuit>::from_bits_le(&value.to_bits_le()).to_bits_le().eject()
        );

        let value = Plaintext::<Circuit>::Interface(
            IndexMap::from_iter(
                vec![
                    (
                        Identifier::new(Mode::Private, "a".try_into()?),
                        Plaintext::<Circuit>::Literal(
                            Literal::Boolean(Boolean::new(Mode::Private, true)),
                            OnceCell::new(),
                        ),
                    ),
                    (
                        Identifier::new(Mode::Private, "b".try_into()?),
                        Plaintext::<Circuit>::Literal(
                            Literal::Field(Field::new(Mode::Private, Uniform::rand(&mut test_rng()))),
                            OnceCell::new(),
                        ),
                    ),
                ]
                .into_iter(),
            ),
            OnceCell::new(),
        );
        assert_eq!(
            value.to_bits_le().eject(),
            Plaintext::<Circuit>::from_bits_le(&value.to_bits_le()).to_bits_le().eject()
        );

        let value = Plaintext::<Circuit>::Interface(
            IndexMap::from_iter(
                vec![
                    (
                        Identifier::new(Mode::Private, "a".try_into()?),
                        Plaintext::<Circuit>::Literal(
                            Literal::Boolean(Boolean::new(Mode::Private, true)),
                            OnceCell::new(),
                        ),
                    ),
                    (
                        Identifier::new(Mode::Private, "b".try_into()?),
                        Plaintext::<Circuit>::Interface(
                            IndexMap::from_iter(
                                vec![
                                    (
                                        Identifier::new(Mode::Private, "c".try_into()?),
                                        Plaintext::<Circuit>::Literal(
                                            Literal::Boolean(Boolean::new(Mode::Private, true)),
                                            OnceCell::new(),
                                        ),
                                    ),
                                    (
                                        Identifier::new(Mode::Private, "d".try_into()?),
                                        Plaintext::<Circuit>::Interface(
                                            IndexMap::from_iter(
                                                vec![
                                                    (
                                                        Identifier::new(Mode::Private, "e".try_into()?),
                                                        Plaintext::<Circuit>::Literal(
                                                            Literal::Boolean(Boolean::new(Mode::Private, true)),
                                                            OnceCell::new(),
                                                        ),
                                                    ),
                                                    (
                                                        Identifier::new(Mode::Private, "f".try_into()?),
                                                        Plaintext::<Circuit>::Literal(
                                                            Literal::Field(Field::new(
                                                                Mode::Private,
                                                                Uniform::rand(&mut test_rng()),
                                                            )),
                                                            OnceCell::new(),
                                                        ),
                                                    ),
                                                ]
                                                .into_iter(),
                                            ),
                                            OnceCell::new(),
                                        ),
                                    ),
                                    (
                                        Identifier::new(Mode::Private, "g".try_into()?),
                                        Plaintext::<Circuit>::Literal(
                                            Literal::Field(Field::new(Mode::Private, Uniform::rand(&mut test_rng()))),
                                            OnceCell::new(),
                                        ),
                                    ),
                                ]
                                .into_iter(),
                            ),
                            OnceCell::new(),
                        ),
                    ),
                    (
                        Identifier::new(Mode::Private, "h".try_into()?),
                        Plaintext::<Circuit>::Literal(
                            Literal::Field(Field::new(Mode::Private, Uniform::rand(&mut test_rng()))),
                            OnceCell::new(),
                        ),
                    ),
                ]
                .into_iter(),
            ),
            OnceCell::new(),
        );
        assert_eq!(
            value.to_bits_le().eject(),
            Plaintext::<Circuit>::from_bits_le(&value.to_bits_le()).to_bits_le().eject()
        );
        Ok(())
    }
}
