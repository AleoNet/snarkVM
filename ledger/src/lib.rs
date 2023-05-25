// Copyright (C) 2019-2023 Aleo Systems Inc.
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

#![forbid(unsafe_code)]

#[macro_use]
extern crate tracing;

mod contains;
mod find;
mod get;
mod iterators;

#[cfg(test)]
mod tests;

use console::{
    account::{Address, GraphKey, PrivateKey, Signature, ViewKey},
    network::prelude::*,
    program::{Ciphertext, Entry, Identifier, Literal, Plaintext, ProgramID, Record, StatePath, Value},
    types::{Field, Group},
};
use synthesizer::{
    block::{Block, ConfirmedTransaction, Header, Transaction, Transactions},
    coinbase::{CoinbaseSolution, EpochChallenge, PuzzleCommitment},
    process::Query,
    program::Program,
    store::{ConsensusStorage, ConsensusStore},
    vm::VM,
};

use aleo_std::prelude::{finish, lap, timer};
use anyhow::Result;
use core::ops::Range;
use indexmap::IndexMap;
use parking_lot::RwLock;
use rand::{prelude::IteratorRandom, rngs::OsRng};
use std::{borrow::Cow, sync::Arc};

#[cfg(not(feature = "serial"))]
use rayon::prelude::*;

pub type RecordMap<N> = IndexMap<Field<N>, Record<N, Plaintext<N>>>;

#[derive(Copy, Clone, Debug)]
pub enum RecordsFilter<N: Network> {
    /// Returns all records associated with the account.
    All,
    /// Returns only records associated with the account that are **spent** with the graph key.
    Spent,
    /// Returns only records associated with the account that are **not spent** with the graph key.
    Unspent,
    /// Returns all records associated with the account that are **spent** with the given private key.
    SlowSpent(PrivateKey<N>),
    /// Returns all records associated with the account that are **not spent** with the given private key.
    SlowUnspent(PrivateKey<N>),
}

#[derive(Clone)]
pub struct Ledger<N: Network, C: ConsensusStorage<N>> {
    /// The VM state.
    vm: VM<N, C>,
    /// The genesis block.
    genesis: Block<N>,
    /// The current block.
    current_block: Arc<RwLock<Block<N>>>,
    /// The current epoch challenge.
    current_epoch_challenge: Arc<RwLock<Option<EpochChallenge<N>>>>,
}

impl<N: Network, C: ConsensusStorage<N>> Ledger<N, C> {
    /// Loads the ledger from storage.
    pub fn load(genesis: Block<N>, dev: Option<u16>) -> Result<Self> {
        let timer = timer!("Ledger::load");

        // Retrieve the genesis hash.
        let genesis_hash = genesis.hash();
        // Initialize the ledger.
        let ledger = Self::load_unchecked(genesis, dev)?;

        // Ensure the ledger contains the correct genesis block.
        if !ledger.contains_block_hash(&genesis_hash)? {
            bail!("Incorrect genesis block (run 'snarkos clean' and try again)")
        }

        // Retrieve the latest height.
        let latest_height =
            *ledger.vm.block_store().heights().max().ok_or_else(|| anyhow!("Failed to load blocks from the ledger"))?;

        // Safety check the existence of `NUM_BLOCKS` random blocks.
        const NUM_BLOCKS: usize = 1000;
        let block_heights: Vec<u32> = (0..=latest_height)
            .choose_multiple(&mut OsRng::default(), core::cmp::min(NUM_BLOCKS, latest_height as usize));
        cfg_into_iter!(block_heights).try_for_each(|height| {
            ledger.get_block(height)?;
            Ok::<_, Error>(())
        })?;
        lap!(timer, "Check existence of {NUM_BLOCKS} random blocks");

        finish!(timer);
        Ok(ledger)
    }

    /// Loads the ledger from storage, without performing integrity checks.
    pub fn load_unchecked(genesis: Block<N>, dev: Option<u16>) -> Result<Self> {
        let timer = timer!("Ledger::load_unchecked");

        // Initialize the consensus store.
        let store = match ConsensusStore::<N, C>::open(dev) {
            Ok(store) => store,
            _ => bail!("Failed to load ledger (run 'snarkos clean' and try again)"),
        };
        lap!(timer, "Load consensus store");

        // Initialize a new VM.
        let vm = VM::from(store)?;
        lap!(timer, "Initialize a new VM");

        // Initialize the ledger.
        let mut ledger = Self {
            vm,
            genesis: genesis.clone(),
            current_block: Arc::new(RwLock::new(genesis.clone())),
            current_epoch_challenge: Default::default(),
        };

        // If the block store is empty, initialize the genesis block.
        if ledger.vm.block_store().heights().max().is_none() {
            // Add the genesis block.
            ledger.add_next_block(&genesis)?;
        }
        lap!(timer, "Initialize genesis");

        // Retrieve the latest height.
        let latest_height =
            *ledger.vm.block_store().heights().max().ok_or_else(|| anyhow!("Failed to load blocks from the ledger"))?;
        // Fetch the latest block.
        let block = ledger
            .get_block(latest_height)
            .map_err(|_| anyhow!("Failed to load block {latest_height} from the ledger"))?;

        // Set the current block.
        ledger.current_block = Arc::new(RwLock::new(block));
        // Set the current epoch challenge.
        ledger.current_epoch_challenge = Arc::new(RwLock::new(Some(ledger.get_epoch_challenge(latest_height)?)));
        lap!(timer, "Initialize ledger");

        finish!(timer);
        Ok(ledger)
    }

    /// Returns the VM.
    pub fn vm(&self) -> &VM<N, C> {
        &self.vm
    }

    /// Returns the latest state root.
    pub fn latest_state_root(&self) -> N::StateRoot {
        self.vm.block_store().current_state_root()
    }

    /// Returns the latest block.
    pub fn latest_block(&self) -> Block<N> {
        self.current_block.read().clone()
    }

    /// Returns the latest round number.
    pub fn latest_round(&self) -> u64 {
        self.current_block.read().round()
    }

    /// Returns the latest block height.
    pub fn latest_height(&self) -> u32 {
        self.current_block.read().height()
    }

    /// Returns the latest block hash.
    pub fn latest_hash(&self) -> N::BlockHash {
        self.current_block.read().hash()
    }

    /// Returns the latest block header.
    pub fn latest_header(&self) -> Header<N> {
        *self.current_block.read().header()
    }

    /// Returns the latest total supply in microcredits.
    pub fn latest_total_supply_in_microcredits(&self) -> u64 {
        self.current_block.read().header().total_supply_in_microcredits()
    }

    /// Returns the latest latest cumulative weight.
    pub fn latest_cumulative_weight(&self) -> u128 {
        self.current_block.read().cumulative_weight()
    }

    /// Returns the latest block coinbase accumulator point.
    pub fn latest_coinbase_accumulator_point(&self) -> Field<N> {
        self.current_block.read().header().coinbase_accumulator_point()
    }

    /// Returns the latest block coinbase target.
    pub fn latest_coinbase_target(&self) -> u64 {
        self.current_block.read().coinbase_target()
    }

    /// Returns the latest block proof target.
    pub fn latest_proof_target(&self) -> u64 {
        self.current_block.read().proof_target()
    }

    /// Returns the last coinbase target.
    pub fn last_coinbase_target(&self) -> u64 {
        self.current_block.read().last_coinbase_target()
    }

    /// Returns the last coinbase timestamp.
    pub fn last_coinbase_timestamp(&self) -> i64 {
        self.current_block.read().last_coinbase_timestamp()
    }

    /// Returns the latest block timestamp.
    pub fn latest_timestamp(&self) -> i64 {
        self.current_block.read().timestamp()
    }

    /// Returns the latest block transactions.
    pub fn latest_transactions(&self) -> Transactions<N> {
        self.current_block.read().transactions().clone()
    }

    /// Returns the latest epoch number.
    pub fn latest_epoch_number(&self) -> u32 {
        self.current_block.read().height() / N::NUM_BLOCKS_PER_EPOCH
    }

    /// Returns the latest epoch challenge.
    pub fn latest_epoch_challenge(&self) -> Result<EpochChallenge<N>> {
        match self.current_epoch_challenge.read().as_ref() {
            Some(challenge) => Ok(challenge.clone()),
            None => self.get_epoch_challenge(self.latest_height()),
        }
    }

    /// Adds the given block as the next block in the chain.
    pub fn add_next_block(&self, block: &Block<N>) -> Result<()> {
        // Acquire the write lock on the current block.
        let mut current_block = self.current_block.write();
        // Update the VM.
        self.vm.add_next_block(block)?;
        // Update the current block.
        *current_block = block.clone();
        // Drop the write lock on the current block.
        drop(current_block);

        // If the block is the start of a new epoch, or the epoch challenge has not been set, update the current epoch challenge.
        if block.height() % N::NUM_BLOCKS_PER_EPOCH == 0 || self.current_epoch_challenge.read().is_none() {
            // Update the current epoch challenge.
            self.current_epoch_challenge.write().clone_from(&self.get_epoch_challenge(block.height()).ok());
        }

        Ok(())
    }

    /// Returns the unspent records.
    pub fn find_unspent_records(&self, view_key: &ViewKey<N>) -> Result<RecordMap<N>> {
        let microcredits = Identifier::from_str("microcredits")?;
        Ok(self
            .find_records(view_key, RecordsFilter::Unspent)?
            .filter(|(_, record)| {
                // TODO (raychu86): Find cleaner approach and check that the record is associated with the `credits.aleo` program
                match record.data().get(&microcredits) {
                    Some(Entry::Private(Plaintext::Literal(Literal::U64(amount), _))) => !amount.is_zero(),
                    _ => false,
                }
            })
            .collect::<IndexMap<_, _>>())
    }

    /// Creates a deploy transaction.
    ///
    /// The `priority_fee_in_microcredits` is an additional fee **on top** of the deployment fee.
    pub fn create_deploy(
        &self,
        private_key: &PrivateKey<N>,
        program: &Program<N>,
        priority_fee_in_microcredits: u64,
        query: Option<Query<N, C::BlockStorage>>,
    ) -> Result<Transaction<N>> {
        // Fetch the unspent records.
        let records = self.find_unspent_records(&ViewKey::try_from(private_key)?)?;
        ensure!(!records.len().is_zero(), "The Aleo account has no records to spend.");
        let mut records = records.values();

        // Initialize an RNG.
        let rng = &mut ::rand::thread_rng();

        // Prepare the fee.
        let fee_record = records.next().unwrap().clone();
        let fee = (fee_record, priority_fee_in_microcredits);

        // Create a new deploy transaction.
        self.vm.deploy(private_key, program, fee, query, rng)
    }

    /// Creates a transfer transaction.
    ///
    /// The `priority_fee_in_microcredits` is an additional fee **on top** of the execution fee.
    pub fn create_transfer(
        &self,
        private_key: &PrivateKey<N>,
        to: Address<N>,
        amount_in_microcredits: u64,
        priority_fee_in_microcredits: u64,
        query: Option<Query<N, C::BlockStorage>>,
    ) -> Result<Transaction<N>> {
        // Fetch the unspent records.
        let records = self.find_unspent_records(&ViewKey::try_from(private_key)?)?;
        ensure!(!records.len().is_zero(), "The Aleo account has no records to spend.");
        let mut records = records.values();

        // Initialize an RNG.
        let rng = &mut rand::thread_rng();

        // Prepare the inputs.
        let inputs = [
            Value::Record(records.next().unwrap().clone()),
            Value::from_str(&format!("{to}"))?,
            Value::from_str(&format!("{amount_in_microcredits}u64"))?,
        ];

        // Prepare the fee.
        let fee_record = records.next().unwrap().clone();
        let fee = Some((fee_record, priority_fee_in_microcredits));

        // Create a new execute transaction.
        self.vm.execute(private_key, ("credits.aleo", "transfer"), inputs.iter(), fee, query, rng)
    }
}
