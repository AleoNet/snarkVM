// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#[cfg(test)]
use snarkvm_circuit_types::environment::assert_scope;

mod encrypt;
mod equal;
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
    /// A plaintext struct.
    Struct(IndexMap<Identifier<A>, Plaintext<A>>, OnceCell<Vec<Boolean<A>>>),
}

#[cfg(console)]
impl<A: Aleo> Inject for Plaintext<A> {
    type Primitive = console::Plaintext<A::Network>;

    /// Initializes a new plaintext circuit from a primitive.
    fn new(mode: Mode, plaintext: Self::Primitive) -> Self {
        match plaintext {
            Self::Primitive::Literal(literal, _) => Self::Literal(Literal::new(mode, literal), Default::default()),
            Self::Primitive::Struct(struct_, _) => Self::Struct(Inject::new(mode, struct_), Default::default()),
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
            Self::Struct(struct_, _) => struct_
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
            Self::Struct(struct_, _) => {
                console::Plaintext::Struct(struct_.iter().map(|pair| pair.eject_value()).collect(), Default::default())
            }
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
    use snarkvm_utilities::{TestRng, Uniform};

    use anyhow::Result;

    #[test]
    fn test_plaintext() -> Result<()> {
        let mut rng = TestRng::default();

        let value = Plaintext::<Circuit>::Literal(Literal::Boolean(Boolean::new(Mode::Private, true)), OnceCell::new());
        assert_eq!(
            value.to_bits_le().eject(),
            Plaintext::<Circuit>::from_bits_le(&value.to_bits_le()).to_bits_le().eject()
        );

        let value = Plaintext::<Circuit>::Literal(
            Literal::Field(Field::new(Mode::Private, Uniform::rand(&mut rng))),
            OnceCell::new(),
        );
        assert_eq!(
            value.to_bits_le().eject(),
            Plaintext::<Circuit>::from_bits_le(&value.to_bits_le()).to_bits_le().eject()
        );

        let value = Plaintext::<Circuit>::Struct(
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
                            Literal::Field(Field::new(Mode::Private, Uniform::rand(&mut rng))),
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

        let value = Plaintext::<Circuit>::Struct(
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
                        Plaintext::<Circuit>::Struct(
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
                                        Plaintext::<Circuit>::Struct(
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
                                                                Uniform::rand(&mut rng),
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
                                            Literal::Field(Field::new(Mode::Private, Uniform::rand(&mut rng))),
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
                            Literal::Field(Field::new(Mode::Private, Uniform::rand(&mut rng))),
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
