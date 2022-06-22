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

use crate::Program;
use console::{
    account::Address,
    network::prelude::*,
    program::{Entry, Identifier, Literal, Plaintext, Record, Register, RegisterType, Value, ValueType},
};

use indexmap::{IndexMap, IndexSet};

#[derive(Clone, PartialEq, Eq)]
pub struct Deploy<N: Network, A: circuit::Aleo<Network = N>> {
    program: Program<N, A>,
}

#[derive(Clone, PartialEq, Eq)]
pub enum Transaction<N: Network, A: circuit::Aleo<Network = N>> {
    Deploy(Deploy<N, A>),
}

#[derive(Clone, PartialEq, Eq)]
pub struct Block<N: Network, A: circuit::Aleo<Network = N>> {
    /// The transactions in this block.
    transactions: Vec<Transaction<N, A>>,
}

#[derive(Clone)]
pub struct Ledger<N: Network, A: circuit::Aleo<Network = N>> {
    /// The mapping of program IDs to their programs.
    programs: IndexMap<u64, Program<N, A>>,
    /// The mapping of program IDs to their global state.
    states: IndexMap<u64, IndexMap<Identifier<N>, Plaintext<N>>>,
    /// The mapping of block numbers to blocks.
    blocks: IndexMap<u32, Block<N, A>>,
    /// The memory pool of unconfirmed transactions.
    memory_pool: IndexSet<Transaction<N, A>>,
}

impl<N: Network, A: circuit::Aleo<Network = N>> Ledger<N, A> {
    /// Initializes a new ledger.
    pub fn new() -> Self {
        Self {
            programs: IndexMap::new(),
            states: IndexMap::new(),
            blocks: IndexMap::new(),
            memory_pool: IndexSet::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use circuit::network::AleoV0;
    use console::{
        account::{PrivateKey, ViewKey},
        network::Testnet3,
    };

    type CurrentNetwork = Testnet3;
    type CurrentAleo = AleoV0;

    #[test]
    fn test_deploy() -> Result<()> {
        // Initialize a new ledger.
        let ledger = Ledger::<CurrentNetwork, CurrentAleo>::new();

        Ok(())
    }
}
