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

mod interface;
pub use interface::Interface;

mod literal_type;
pub use literal_type::LiteralType;

use crate::Identifier;
use snarkvm_console_network::prelude::*;

use anyhow::{bail, Result};
use core::ops::Deref;

/// The declared layout for program data.
#[derive(Clone, PartialEq, Eq)]
pub struct DataType<N: Network>(Vec<(Identifier<N>, Entry<N>)>);

impl<N: Network> TryFrom<Vec<(Identifier<N>, Entry<N>)>> for DataType<N> {
    type Error = Error;

    /// Initializes a new `DataType` from a vector of `(Identifier, Entry)` pairs.
    fn try_from(entries: Vec<(Identifier<N>, Entry<N>)>) -> Result<Self> {
        // Ensure the number of entries is within `N::MAX_DATA_ENTRIES`.
        match entries.len() <= N::MAX_DATA_ENTRIES {
            true => Ok(Self(entries)),
            false => bail!("Data exceeds size: expected <= {}, found {}", N::MAX_DATA_ENTRIES, entries.len()),
        }
    }
}
