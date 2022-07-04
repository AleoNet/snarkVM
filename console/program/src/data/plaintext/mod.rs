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

mod bytes;
mod encrypt;
mod find;
mod from_bits;
mod from_fields;
mod num_randomizers;
mod parse;
mod serialize;
mod size_in_fields;
mod to_bits;
mod to_fields;

use crate::{Ciphertext, Identifier, Literal};
use snarkvm_console_network::Network;
use snarkvm_console_types::prelude::*;

use indexmap::IndexMap;
use once_cell::sync::OnceCell;

#[derive(Clone)]
pub enum Plaintext<N: Network> {
    /// A literal.
    Literal(Literal<N>, OnceCell<Vec<bool>>),
    /// A interface.
    Interface(IndexMap<Identifier<N>, Plaintext<N>>, OnceCell<Vec<bool>>),
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

impl<N: Network> PartialEq for Plaintext<N> {
    /// Returns `true` if `self` and `other` are equal.
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Literal(l1, _), Self::Literal(l2, _)) => l1 == l2,
            (Self::Interface(i1, _), Self::Interface(i2, _)) => i1 == i2,
            _ => false,
        }
    }
}

impl<N: Network> Eq for Plaintext<N> {}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;
    use snarkvm_console_types::Field;

    use core::str::FromStr;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_plaintext() -> Result<()> {
        let value = Plaintext::<CurrentNetwork>::from_str("true")?;
        assert_eq!(value.to_bits_le(), Plaintext::<CurrentNetwork>::from_bits_le(&value.to_bits_le())?.to_bits_le());

        let value = Plaintext::<CurrentNetwork>::Literal(
            Literal::Field(Field::new(Uniform::rand(&mut test_rng()))),
            OnceCell::new(),
        );
        assert_eq!(value.to_bits_le(), Plaintext::<CurrentNetwork>::from_bits_le(&value.to_bits_le())?.to_bits_le());

        let value = Plaintext::<CurrentNetwork>::Interface(
            IndexMap::from_iter(
                vec![
                    (Identifier::from_str("a")?, Plaintext::<CurrentNetwork>::from_str("true")?),
                    (
                        Identifier::from_str("b")?,
                        Plaintext::<CurrentNetwork>::Literal(
                            Literal::Field(Field::new(Uniform::rand(&mut test_rng()))),
                            OnceCell::new(),
                        ),
                    ),
                ]
                .into_iter(),
            ),
            OnceCell::new(),
        );
        assert_eq!(value.to_bits_le(), Plaintext::<CurrentNetwork>::from_bits_le(&value.to_bits_le())?.to_bits_le());

        let value = Plaintext::<CurrentNetwork>::Interface(
            IndexMap::from_iter(
                vec![
                    (Identifier::from_str("a")?, Plaintext::<CurrentNetwork>::from_str("true")?),
                    (
                        Identifier::from_str("b")?,
                        Plaintext::<CurrentNetwork>::Interface(
                            IndexMap::from_iter(
                                vec![
                                    (Identifier::from_str("c")?, Plaintext::<CurrentNetwork>::from_str("true")?),
                                    (
                                        Identifier::from_str("d")?,
                                        Plaintext::<CurrentNetwork>::Interface(
                                            IndexMap::from_iter(
                                                vec![
                                                    (
                                                        Identifier::from_str("e")?,
                                                        Plaintext::<CurrentNetwork>::from_str("true")?,
                                                    ),
                                                    (
                                                        Identifier::from_str("f")?,
                                                        Plaintext::<CurrentNetwork>::Literal(
                                                            Literal::Field(Field::new(Uniform::rand(&mut test_rng()))),
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
                                        Identifier::from_str("g")?,
                                        Plaintext::<CurrentNetwork>::Literal(
                                            Literal::Field(Field::new(Uniform::rand(&mut test_rng()))),
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
                        Identifier::from_str("h")?,
                        Plaintext::<CurrentNetwork>::Literal(
                            Literal::Field(Field::new(Uniform::rand(&mut test_rng()))),
                            OnceCell::new(),
                        ),
                    ),
                ]
                .into_iter(),
            ),
            OnceCell::new(),
        );
        assert_eq!(value.to_bits_le(), Plaintext::<CurrentNetwork>::from_bits_le(&value.to_bits_le())?.to_bits_le());
        Ok(())
    }
}
