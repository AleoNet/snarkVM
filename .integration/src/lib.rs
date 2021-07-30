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

pub mod testnet1;
pub use testnet1::*;

pub mod testnet2;
pub use testnet2::*;

use snarkvm_dpc::prelude::*;
use snarkvm_ledger::prelude::*;

use rand::Rng;

pub fn random_storage_path() -> String {
    let random_path: usize = rand::thread_rng().gen();
    format!("./test_db-{}", random_path)
}

/// Initializes a test ledger given a genesis block.
pub fn initialize_test_blockchain<C: Parameters, S: Storage>(genesis_block: Block<Transaction<C>>) -> Ledger<C, S> {
    let mut path = std::env::temp_dir();
    path.push(random_storage_path());

    Ledger::new(Some(&path), genesis_block).unwrap()
}
