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

mod literal_type;
pub use literal_type::LiteralType;

mod plaintext_type;
pub use plaintext_type::PlaintextType;

mod value_type;
pub use value_type::ValueType;

mod bytes;
mod parse;

use crate::Identifier;
use snarkvm_console_network::prelude::*;
use snarkvm_utilities::{
    error,
    has_duplicates,
    io::{Read, Result as IoResult, Write},
    FromBytes,
    ToBytes,
};

use indexmap::IndexMap;

/// The declared layout for program data.
#[derive(Clone, PartialEq, Eq)]
pub struct RecordType<N: Network> {
    /// The name of the record type.
    name: Identifier<N>,
    /// The name and value type for the entries in data.
    entries: IndexMap<Identifier<N>, ValueType<N>>,
}

impl<N: Network> RecordType<N> {
    /// Returns the name of the record type.
    #[inline]
    pub const fn name(&self) -> &Identifier<N> {
        &self.name
    }

    /// Returns the entries of the record type.
    #[inline]
    pub const fn entries(&self) -> &IndexMap<Identifier<N>, ValueType<N>> {
        &self.entries
    }
}

impl<N: Network> TryFrom<(Identifier<N>, IndexMap<Identifier<N>, ValueType<N>>)> for RecordType<N> {
    type Error = Error;

    /// Initializes a new `RecordType` from a map of `(Identifier, ValueType)` pairs.
    fn try_from((name, entries): (Identifier<N>, IndexMap<Identifier<N>, ValueType<N>>)) -> Result<Self> {
        // Ensure the number of entries is within `N::MAX_DATA_ENTRIES`.
        match entries.len() <= N::MAX_DATA_ENTRIES {
            true => Ok(Self { name, entries }),
            false => bail!("Data exceeds size: expected <= {}, found {}", N::MAX_DATA_ENTRIES, entries.len()),
        }
    }
}

impl<N: Network> TypeName for RecordType<N> {
    /// Returns the type name.
    fn type_name() -> &'static str {
        "record"
    }
}
