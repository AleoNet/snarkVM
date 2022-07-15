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

mod entry;
pub use entry::Entry;

mod helpers;
pub use helpers::{Balance, Owner};

mod bytes;
mod decrypt;
mod encrypt;
mod find;
mod num_randomizers;
mod parse_ciphertext;
mod parse_plaintext;
mod serialize;
mod to_bits;
mod to_commitment;
mod to_fields;

use crate::{Ciphertext, Identifier, Literal, Plaintext, ProgramID};
use snarkvm_console_account::{Address, ViewKey};
use snarkvm_console_network::prelude::*;
use snarkvm_console_types::{Field, Group, Scalar, U64};

use indexmap::IndexMap;

/// A value stored in program record.
#[derive(Clone, PartialEq, Eq)]
pub struct Record<N: Network, Private: Visibility> {
    /// The owner of the program record.
    owner: Owner<N, Private>,
    /// The Aleo balance (in gates) of the program record.
    gates: Balance<N, Private>,
    /// The program data.
    data: IndexMap<Identifier<N>, Entry<N, Private>>,
}

impl<N: Network> Record<N, Plaintext<N>> {
    /// Initializes a new record.
    pub fn from_plaintext(
        owner: Owner<N, Plaintext<N>>,
        gates: Balance<N, Plaintext<N>>,
        data: IndexMap<Identifier<N>, Entry<N, Plaintext<N>>>,
    ) -> Result<Self> {
        // Ensure the members has no duplicate names.
        ensure!(!has_duplicates(data.iter().map(|(name, ..)| name)), "A duplicate entry name was found in a record");
        // Ensure the number of interfaces is within `N::MAX_DATA_ENTRIES`.
        ensure!(data.len() <= N::MAX_DATA_ENTRIES, "Found a record that exceeds size ({})", data.len());
        // Return the record.
        Ok(Self { owner, gates, data })
    }
}

impl<N: Network> Record<N, Ciphertext<N>> {
    /// Initializes a new record.
    pub fn from_ciphertext(
        owner: Owner<N, Ciphertext<N>>,
        gates: Balance<N, Ciphertext<N>>,
        data: IndexMap<Identifier<N>, Entry<N, Ciphertext<N>>>,
    ) -> Result<Self> {
        // Ensure the members has no duplicate names.
        ensure!(!has_duplicates(data.iter().map(|(name, ..)| name)), "A duplicate entry name was found in a record");
        // Ensure the number of interfaces is within `N::MAX_DATA_ENTRIES`.
        ensure!(data.len() <= N::MAX_DATA_ENTRIES, "Found a record that exceeds size ({})", data.len());
        // Return the record.
        Ok(Self { owner, gates, data })
    }
}

impl<N: Network, Private: Visibility> Record<N, Private> {
    /// Returns the owner of the program record.
    pub const fn owner(&self) -> &Owner<N, Private> {
        &self.owner
    }

    /// Returns the gates of the program record.
    pub const fn gates(&self) -> &Balance<N, Private> {
        &self.gates
    }

    /// Returns the program data.
    pub const fn data(&self) -> &IndexMap<Identifier<N>, Entry<N, Private>> {
        &self.data
    }
}
