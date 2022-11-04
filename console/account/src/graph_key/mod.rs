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
mod serialize;
mod string;
mod try_from;

#[cfg(feature = "view_key")]
use crate::ViewKey;

use snarkvm_console_network::prelude::*;
use snarkvm_console_types::Field;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct GraphKey<N: Network> {
    /// The graph key `sk_tag` := Hash(view_key || ctr).
    sk_tag: Field<N>,
}

impl<N: Network> GraphKey<N> {
    /// Returns the graph key.
    pub const fn sk_tag(&self) -> Field<N> {
        self.sk_tag
    }
}
