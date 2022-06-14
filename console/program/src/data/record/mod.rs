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
use helpers::{Balance, Owner};

mod decrypt;
mod encrypt;
mod find;
mod num_randomizers;
mod parse;
mod to_bits;
mod to_id;

use crate::{Ciphertext, Identifier, Literal, Plaintext, Visibility};
use snarkvm_console_account::{Address, ViewKey};
use snarkvm_console_network::prelude::*;
use snarkvm_console_types::{Field, Group, Scalar, U64};

use indexmap::IndexMap;

/// A value stored in program record.
#[derive(Clone, PartialEq, Eq)]
pub struct Record<N: Network, Private: Visibility> {
    /// The owner of the program record.
    owner: Owner<N, Private>,
    /// The balance of the program record.
    balance: Balance<N, Private>,
    /// The program data.
    data: IndexMap<Identifier<N>, Entry<N, Private>>,
}

impl<N: Network> Record<N, Plaintext<N>> {
    /// Returns the owner of the program record.
    pub fn owner(&self) -> Address<N> {
        *self.owner
    }

    /// Returns the balance of the program record.
    pub fn balance(&self) -> U64<N> {
        *self.balance
    }
}

impl<N: Network, Private: Visibility> Record<N, Private> {
    /// Returns the program data.
    pub const fn data(&self) -> &IndexMap<Identifier<N>, Entry<N, Private>> {
        &self.data
    }
}
