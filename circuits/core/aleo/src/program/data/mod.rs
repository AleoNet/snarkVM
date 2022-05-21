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

// #[cfg(test)]
// use snarkvm_circuits_types::environment::assert_scope;

mod decrypt;
mod encrypt;
mod to_data_id;

use crate::Aleo;
use snarkvm_circuits_types::{environment::prelude::*, Address, Boolean, Field, Group, Scalar};

/// A general purpose data structure for representing program data in a record.
pub trait DataType<A: Aleo>: Clone + Eject + ToBits<Boolean = Boolean<A>> + FromBits<Boolean = Boolean<A>> {}

#[derive(Clone)]
pub enum Data<A: Aleo, D: DataType<A>> {
    /// Publicly-visible data.
    Plaintext(D, Mode),
    /// Private data encrypted under the account owner's address.
    Ciphertext(Vec<Field<A>>, Mode),
}

impl<A: Aleo, D: DataType<A>> Data<A, D> {
    /// Returns the mode of the data.
    pub fn mode(&self) -> Mode {
        match self {
            Self::Plaintext(_, mode) => *mode,
            Self::Ciphertext(_, mode) => *mode,
        }
    }

    /// Returns `true` if the enum variant corresponds to the correct mode.
    /// Otherwise, the method returns `false`.
    pub fn is_valid(&self) -> bool {
        match self {
            Self::Plaintext(_, mode) => mode.is_constant() || mode.is_public(),
            Self::Ciphertext(_, mode) => mode.is_private(),
        }
    }
}

impl<A: Aleo, D: DataType<A>> TypeName for Data<A, D> {
    fn type_name() -> &'static str {
        "data"
    }
}
