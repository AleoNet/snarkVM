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

mod key;
use key::*;

mod value;
use value::*;

mod bytes;
mod parse;

use console::{network::prelude::*, program::Identifier};

#[derive(Clone, PartialEq, Eq)]
pub struct Mapping<N: Network> {
    /// The name of the mapping.
    name: Identifier<N>,
    /// The key statement.
    key: MapKey<N>,
    /// The value statement.
    value: MapValue<N>,
}

impl<N: Network> Mapping<N> {
    /// Initializes a new mapping with the given name, key statement, and value statement.
    pub fn new(name: Identifier<N>, key: MapKey<N>, value: MapValue<N>) -> Self {
        Self { name, key, value }
    }

    /// Returns the name of the mapping.
    pub const fn name(&self) -> &Identifier<N> {
        &self.name
    }

    /// Returns the key statement.
    pub const fn key(&self) -> &MapKey<N> {
        &self.key
    }

    /// Returns the value statement.
    pub const fn value(&self) -> &MapValue<N> {
        &self.value
    }
}

impl<N: Network> TypeName for Mapping<N> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "mapping"
    }
}
