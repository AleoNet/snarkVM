// Copyright (C) 2019-2023 Aleo Systems Inc.
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

mod finalize;
pub use finalize::*;

use console::{network::Network, types::Field};

/// Enum to represent the allowed set of Merkle tree operations.
#[derive(Clone, Debug)]
pub enum FinalizeOperation<N: Network> {
    /// Appends a mapping to the program tree, as (`mapping ID`).
    InitializeMapping(Field<N>),
    /// Inserts a key-value leaf into the mapping tree,
    /// as (`mapping ID`, `key ID`, `value ID`).
    InsertKeyValue(Field<N>, Field<N>, Field<N>),
    /// Updates the key-value leaf at the given index in the mapping tree,
    /// as (`mapping ID`, `index`, `key ID`, `value ID`).
    UpdateKeyValue(Field<N>, usize, Field<N>, Field<N>),
    /// Removes the key-value leaf at the given index in the mapping tree,
    /// as (`mapping ID`, `index`).
    RemoveKeyValue(Field<N>, usize),
    /// Removes a mapping from the program tree, as (`mapping ID`).
    RemoveMapping(Field<N>),
}
