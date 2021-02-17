// Copyright (C) 2019-2021 Aleo Systems Inc.
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

mod mem;
pub use mem::MemDb;

use snarkvm_models::{
    algorithms::merkle_tree::LoadableMerkleParameters,
    objects::{LedgerScheme, Storage, Transaction},
};
use snarkvm_objects::Block;
pub use snarkvm_storage::Ledger;

// Initialize a test blockchain given genesis attributes
pub fn initialize_test_blockchain<T: Transaction, P: LoadableMerkleParameters, S: Storage>(
    parameters: P,
    genesis_block: Block<T>,
) -> Ledger<T, P, S> {
    Ledger::<T, P, S>::new(None, parameters, genesis_block).unwrap()
}
