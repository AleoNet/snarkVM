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
#![warn(clippy::cast_possible_truncation)]

#[macro_use]
extern crate tracing;

pub use ledger_authority as authority;
pub use ledger_block as block;
pub use ledger_coinbase as coinbase;
pub use ledger_narwhal as narwhal;
pub use ledger_query as query;
pub use ledger_store as store;

pub use crate::block::*;

mod helpers;
pub use helpers::*;

mod advance;
mod check_next_block;
mod check_transaction_basic;
mod contains;
mod find;
mod get;
mod iterators;

#[cfg(test)]
mod tests;

use console::{
    account::{Address, GraphKey, PrivateKey, ViewKey},
    network::prelude::*,
    program::{
        Ciphertext,
        Entry,
        Identifier,
        Literal,
        Plaintext,
        ProgramID,
        Record,
        StatePath,
        Value,
        RATIFICATIONS_DEPTH,
    },
    types::{Field, Group},
};
use ledger_authority::Authority;
use ledger_block::{Block, ConfirmedTransaction, Header, Metadata, Ratify, Transaction, Transactions};
use ledger_coinbase::{CoinbasePuzzle, CoinbaseSolution, EpochChallenge, ProverSolution, PuzzleCommitment};
use ledger_narwhal::{BatchCertificate, Transmission, TransmissionID};
use ledger_query::Query;
use ledger_store::{ConsensusStorage, ConsensusStore};
use synthesizer::{
    program::{FinalizeGlobalState, Program},
    vm::VM,
};

use aleo_std::prelude::{finish, lap, timer};
use anyhow::Result;
use core::ops::Range;
use indexmap::{IndexMap, IndexSet};
use parking_lot::RwLock;
use rand::{prelude::IteratorRandom, rngs::OsRng, SeedableRng};
use std::{borrow::Cow, collections::BTreeMap, sync::Arc};
use time::OffsetDateTime;

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
    /// The coinbase puzzle.
    coinbase_puzzle: CoinbasePuzzle<N>,
    /// The current block.
    current_block: Arc<RwLock<Block<N>>>,
    /// The current epoch challenge.
    current_epoch_challenge: Arc<RwLock<Option<EpochChallenge<N>>>>,
    /// The current committee.
    current_committee: Arc<RwLock<IndexSet<Address<N>>>>,
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
            coinbase_puzzle: CoinbasePuzzle::<N>::load()?,
            current_block: Arc::new(RwLock::new(genesis.clone())),
            current_epoch_challenge: Default::default(),
            current_committee: Default::default(),
        };

        // Add the genesis validator to the committee.
        ledger.current_committee.write().insert(genesis.authority().to_address());

        // If the block store is empty, initialize the genesis block.
        if ledger.vm.block_store().heights().max().is_none() {
            // Add the genesis block.
            ledger.advance_to_next_block(&genesis)?;
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

    /// TODO: Delete this after testing for snarkOS team.
    pub fn insert_committee_member(&self, address: Address<N>) {
        self.current_committee.write().insert(address);
    }

    /// Returns the VM.
    pub const fn vm(&self) -> &VM<N, C> {
        &self.vm
    }

    /// Returns the coinbase puzzle.
    pub const fn coinbase_puzzle(&self) -> &CoinbasePuzzle<N> {
        &self.coinbase_puzzle
    }

    /// Returns the latest committee.
    pub fn latest_committee(&self) -> IndexSet<Address<N>> {
        self.current_committee.read().clone()
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
}

impl<N: Network, C: ConsensusStorage<N>> Ledger<N, C> {
    /// Returns the unspent `credits.aleo` records.
    pub fn find_unspent_credits_records(&self, view_key: &ViewKey<N>) -> Result<RecordMap<N>> {
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
        let records = self.find_unspent_credits_records(&ViewKey::try_from(private_key)?)?;
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
        let records = self.find_unspent_credits_records(&ViewKey::try_from(private_key)?)?;
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
        self.vm.execute(private_key, ("credits.aleo", "transfer_private"), inputs.iter(), fee, query, rng)
    }
}

#[cfg(test)]
pub(crate) mod test_helpers {
    use crate::Ledger;
    use console::{
        account::{Address, PrivateKey, ViewKey},
        network::Testnet3,
        prelude::*,
    };
    use ledger_block::Block;
    use ledger_store::{helpers::memory::ConsensusMemory, ConsensusStore};
    use synthesizer::vm::VM;

    pub(crate) type CurrentNetwork = Testnet3;
    pub(crate) type CurrentLedger = Ledger<CurrentNetwork, ConsensusMemory<CurrentNetwork>>;

    #[allow(dead_code)]
    pub(crate) struct TestEnv {
        pub ledger: CurrentLedger,
        pub private_key: PrivateKey<CurrentNetwork>,
        pub view_key: ViewKey<CurrentNetwork>,
        pub address: Address<CurrentNetwork>,
    }

    pub(crate) fn sample_test_env(rng: &mut (impl Rng + CryptoRng)) -> TestEnv {
        // Sample the genesis private key.
        let private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let view_key = ViewKey::try_from(&private_key).unwrap();
        let address = Address::try_from(&private_key).unwrap();
        // Sample the ledger.
        let ledger = sample_ledger(private_key, rng);
        // Return the test environment.
        TestEnv { ledger, private_key, view_key, address }
    }

    pub(crate) fn sample_genesis_block() -> Block<CurrentNetwork> {
        Block::<CurrentNetwork>::from_bytes_le(CurrentNetwork::genesis_bytes()).unwrap()
    }

    pub(crate) fn sample_ledger(
        private_key: PrivateKey<CurrentNetwork>,
        rng: &mut (impl Rng + CryptoRng),
    ) -> CurrentLedger {
        // Initialize the store.
        let store = ConsensusStore::<_, ConsensusMemory<_>>::open(None).unwrap();
        // Create a genesis block.
        let genesis = VM::from(store).unwrap().genesis(&private_key, rng).unwrap();
        // Initialize the ledger with the genesis block.
        let ledger = CurrentLedger::load(genesis.clone(), None).unwrap();
        // Ensure the genesis block is correct.
        assert_eq!(genesis, ledger.get_block(0).unwrap());
        // Return the ledger.
        ledger
    }
}
