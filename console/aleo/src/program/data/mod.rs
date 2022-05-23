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

use crate::{
    program::{Ciphertext, Plaintext},
    Address,
    Entry,
    Identifier,
    Network,
    ViewKey,
    Visibility,
};
use snarkvm_curves::{AffineCurve, ProjectiveCurve};

use anyhow::{bail, Result};

/// A value stored in program data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Data<N: Network, Private: Visibility<N>>(Vec<(Identifier<N>, Entry<N, Private>)>);

impl<N: Network, Private: Visibility<N>> From<Vec<(Identifier<N>, Entry<N, Private>)>> for Data<N, Private> {
    /// Initializes a new `Data` value from a vector of `(Identifier, Entry)` pairs.
    fn from(entries: Vec<(Identifier<N>, Entry<N, Private>)>) -> Self {
        Self(entries)
    }
}

impl<N: Network> Data<N, Ciphertext<N>> {
    /// Returns the data ID, as a hash over the **`Data<N, Ciphertext<N>>` variant**.
    pub fn to_id(&self) -> Result<N::Field> {
        // for entry in &self.data {
        //     match entry {
        //         Entry::Constant(plaintext) => match plaintext {
        //             Plaintext::Literal(literal) => literal.to_bytes_le(),
        //             Plaintext::Composite(composite) =>
        //         },
        //         Entry::Public(plaintext) => ,
        //         Entry::Private(ciphertext) => ,
        //     }
        //
        // }

        // N::hash_psd8([self.data])
        use snarkvm_fields::Zero;
        Ok(N::Field::zero())
    }
}

impl<N: Network> Data<N, Plaintext<N>> {
    /// Returns the data ID, as a hash over the **`Data<N, Ciphertext<N>>` variant**.
    pub fn to_id(&self) -> Result<N::Field> {
        bail!("Illegal operation: Data::to_id() cannot be invoked on the `Plaintext<N>` variant.")
    }
}
