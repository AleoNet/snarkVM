// Copyright 2024 Aleo Network Foundation
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
