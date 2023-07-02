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
// #![warn(clippy::cast_possible_truncation)]

pub mod header;
pub use header::*;

pub mod ratify;
pub use ratify::*;

pub mod transaction;
pub use transaction::*;

pub mod transactions;
pub use transactions::*;

pub mod transition;
pub use transition::*;

mod bytes;
mod genesis;
mod serialize;
mod string;

use console::{
    account::{PrivateKey, Signature},
    network::prelude::*,
    program::{Ciphertext, Record},
    types::{Field, Group, U64},
};
use synthesizer_coinbase::{CoinbaseSolution, PuzzleCommitment};

#[derive(Clone, PartialEq, Eq)]
pub struct Block<N: Network> {
    /// The hash of this block.
    block_hash: N::BlockHash,
    /// The hash of the previous block.
    previous_hash: N::BlockHash,
    /// The header of this block.
    header: Header<N>,
    /// The transactions in this block.
    transactions: Transactions<N>,
    /// The ratifications in this block.
    ratifications: Vec<Ratify<N>>,
    /// The coinbase solution.
    coinbase: Option<CoinbaseSolution<N>>,
    /// The signature for this block.
    signature: Signature<N>,
}

impl<N: Network> Block<N> {
    /// Initializes a new block from a given previous hash, header, transactions, ratifications, coinbase, and signature.
    pub fn new<R: Rng + CryptoRng>(
        private_key: &PrivateKey<N>,
        previous_hash: N::BlockHash,
        header: Header<N>,
        transactions: Transactions<N>,
        ratifications: Vec<Ratify<N>>,
        coinbase: Option<CoinbaseSolution<N>>,
        rng: &mut R,
    ) -> Result<Self> {
        // Ensure the block is not empty.
        ensure!(!transactions.is_empty(), "Cannot create a block with zero transactions.");
        // Compute the block hash.
        let block_hash = N::hash_bhp1024(&[previous_hash.to_bits_le(), header.to_root()?.to_bits_le()].concat())?;
        // Sign the block hash.
        let signature = private_key.sign(&[block_hash], rng)?;
        // Construct the block.
        Self::from(previous_hash, header, transactions, ratifications, coinbase, signature)
    }

    /// Initializes a new block from a given previous hash, header, transactions, ratifications, coinbase, and signature.
    pub fn from(
        previous_hash: N::BlockHash,
        header: Header<N>,
        transactions: Transactions<N>,
        ratifications: Vec<Ratify<N>>,
        coinbase: Option<CoinbaseSolution<N>>,
        signature: Signature<N>,
    ) -> Result<Self> {
        // Ensure the block is not empty.
        ensure!(!transactions.is_empty(), "Cannot create a block with zero transactions.");
        // Compute the block hash.
        let block_hash = N::hash_bhp1024(&[previous_hash.to_bits_le(), header.to_root()?.to_bits_le()].concat())?;
        // Derive the signer address.
        let address = signature.to_address();
        // Ensure the signature is valid.
        ensure!(signature.verify(&address, &[block_hash]), "Invalid signature for block {}", header.height());

        // Ensure that coinbase accumulator matches the coinbase solution.
        let expected_accumulator_point = match &coinbase {
            Some(coinbase_solution) => coinbase_solution.to_accumulator_point()?,
            None => Field::<N>::zero(),
        };
        ensure!(
            header.coinbase_accumulator_point() == expected_accumulator_point,
            "The coinbase accumulator point in the block header does not correspond to the given coinbase solution"
        );

        // Construct the block.
        Ok(Self {
            block_hash: block_hash.into(),
            previous_hash,
            header,
            transactions,
            ratifications,
            coinbase,
            signature,
        })
    }
}

impl<N: Network> Block<N> {
    /// Returns the block hash.
    pub const fn hash(&self) -> N::BlockHash {
        self.block_hash
    }

    /// Returns the previous block hash.
    pub const fn previous_hash(&self) -> N::BlockHash {
        self.previous_hash
    }

    /// Returns the ratifications in this block.
    pub const fn ratifications(&self) -> &Vec<Ratify<N>> {
        &self.ratifications
    }

    /// Returns the coinbase solution.
    pub const fn coinbase(&self) -> Option<&CoinbaseSolution<N>> {
        self.coinbase.as_ref()
    }

    /// Returns the signature.
    pub const fn signature(&self) -> &Signature<N> {
        &self.signature
    }
}

impl<N: Network> Block<N> {
    /// Returns the block header.
    pub const fn header(&self) -> &Header<N> {
        &self.header
    }

    /// Returns the previous state root from the block header.
    pub const fn previous_state_root(&self) -> Field<N> {
        self.header.previous_state_root()
    }

    /// Returns the transactions root in the block header.
    pub const fn transactions_root(&self) -> Field<N> {
        self.header.transactions_root()
    }

    /// Returns the finalize root in the block header.
    pub const fn finalize_root(&self) -> Field<N> {
        self.header.finalize_root()
    }

    /// Returns the ratifications root in the block header.
    pub const fn ratifications_root(&self) -> Field<N> {
        self.header.ratifications_root()
    }

    /// Returns the coinbase accumulator point in the block header.
    pub const fn coinbase_accumulator_point(&self) -> Field<N> {
        self.header.coinbase_accumulator_point()
    }

    /// Returns the metadata in the block header.
    pub const fn metadata(&self) -> &Metadata<N> {
        self.header.metadata()
    }

    /// Returns the network ID of this block.
    pub const fn network(&self) -> u16 {
        self.header.network()
    }

    /// Returns the height of this block.
    pub const fn height(&self) -> u32 {
        self.header.height()
    }

    /// Returns the round number of this block.
    pub const fn round(&self) -> u64 {
        self.header.round()
    }

    /// Returns the epoch number of this block.
    pub const fn epoch_number(&self) -> u32 {
        self.height() / N::NUM_BLOCKS_PER_EPOCH
    }

    /// Returns the total supply of microcredits at this block.
    pub const fn total_supply_in_microcredits(&self) -> u64 {
        self.header.total_supply_in_microcredits()
    }

    /// Returns the cumulative weight for this block.
    pub const fn cumulative_weight(&self) -> u128 {
        self.header.cumulative_weight()
    }

    /// Returns the cumulative proof target for this block.
    pub const fn cumulative_proof_target(&self) -> u128 {
        self.header.cumulative_proof_target()
    }

    /// Returns the coinbase target for this block.
    pub const fn coinbase_target(&self) -> u64 {
        self.header.coinbase_target()
    }

    /// Returns the proof target for this block.
    pub const fn proof_target(&self) -> u64 {
        self.header.proof_target()
    }

    /// Returns the coinbase target of the last coinbase.
    pub const fn last_coinbase_target(&self) -> u64 {
        self.header.last_coinbase_target()
    }

    /// Returns the Unix timestamp (UTC) of the last coinbase.
    pub const fn last_coinbase_timestamp(&self) -> i64 {
        self.header.last_coinbase_timestamp()
    }

    /// Returns the Unix timestamp (UTC) for this block.
    pub const fn timestamp(&self) -> i64 {
        self.header.timestamp()
    }
}

impl<N: Network> Block<N> {
    /// Returns `true` if the block contains the given transition ID.
    pub fn contains_transition(&self, transition_id: &N::TransitionID) -> bool {
        self.transactions.contains_transition(transition_id)
    }

    /// Returns `true` if the block contains the given serial number.
    pub fn contains_serial_number(&self, serial_number: &Field<N>) -> bool {
        self.transactions.contains_serial_number(serial_number)
    }

    /// Returns `true` if the block contains the given commitment.
    pub fn contains_commitment(&self, commitment: &Field<N>) -> bool {
        self.transactions.contains_commitment(commitment)
    }
}

impl<N: Network> Block<N> {
    /// Returns the transaction with the given transition ID, if it exists.
    pub fn find_transaction_for_transition_id(&self, transition_id: &N::TransitionID) -> Option<&Transaction<N>> {
        self.transactions.find_transaction_for_transition_id(transition_id)
    }

    /// Returns the transaction with the given serial number, if it exists.
    pub fn find_transaction_for_serial_number(&self, serial_number: &Field<N>) -> Option<&Transaction<N>> {
        self.transactions.find_transaction_for_serial_number(serial_number)
    }

    /// Returns the transaction with the given commitment, if it exists.
    pub fn find_transaction_for_commitment(&self, commitment: &Field<N>) -> Option<&Transaction<N>> {
        self.transactions.find_transaction_for_commitment(commitment)
    }

    /// Returns the transition with the corresponding transition ID, if it exists.
    pub fn find_transition(&self, transition_id: &N::TransitionID) -> Option<&Transition<N>> {
        self.transactions.find_transition(transition_id)
    }

    /// Returns the transition for the given serial number, if it exists.
    pub fn find_transition_for_serial_number(&self, serial_number: &Field<N>) -> Option<&Transition<N>> {
        self.transactions.find_transition_for_serial_number(serial_number)
    }

    /// Returns the transition for the given commitment, if it exists.
    pub fn find_transition_for_commitment(&self, commitment: &Field<N>) -> Option<&Transition<N>> {
        self.transactions.find_transition_for_commitment(commitment)
    }

    /// Returns the record with the corresponding commitment, if it exists.
    pub fn find_record(&self, commitment: &Field<N>) -> Option<&Record<N, Ciphertext<N>>> {
        self.transactions.find_record(commitment)
    }
}

impl<N: Network> Block<N> {
    /// Returns the puzzle commitments in this block.
    pub fn puzzle_commitments(&self) -> Option<impl '_ + Iterator<Item = PuzzleCommitment<N>>> {
        self.coinbase.as_ref().map(|solution| solution.puzzle_commitments())
    }

    /// Returns the transactions in this block.
    pub const fn transactions(&self) -> &Transactions<N> {
        &self.transactions
    }

    /// Returns an iterator over the transaction IDs, for all transactions in `self`.
    pub fn transaction_ids(&self) -> impl '_ + Iterator<Item = &N::TransactionID> {
        self.transactions.transaction_ids()
    }

    /// Returns an iterator over all transactions in `self` that are accepted deploy transactions.
    pub fn deployments(&self) -> impl '_ + Iterator<Item = &ConfirmedTransaction<N>> {
        self.transactions.deployments()
    }

    /// Returns an iterator over all transactions in `self` that are accepted execute transactions.
    pub fn executions(&self) -> impl '_ + Iterator<Item = &ConfirmedTransaction<N>> {
        self.transactions.executions()
    }

    /// Returns an iterator over all transitions.
    pub fn transitions(&self) -> impl '_ + Iterator<Item = &Transition<N>> {
        self.transactions.transitions()
    }

    /// Returns an iterator over the transition IDs, for all transitions.
    pub fn transition_ids(&self) -> impl '_ + Iterator<Item = &N::TransitionID> {
        self.transactions.transition_ids()
    }

    /// Returns an iterator over the transition public keys, for all transactions.
    pub fn transition_public_keys(&self) -> impl '_ + Iterator<Item = &Group<N>> {
        self.transactions.transition_public_keys()
    }

    /// Returns an iterator over the transition commitments, for all transactions.
    pub fn transition_commitments(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.transactions.transition_commitments()
    }

    /// Returns an iterator over the tags, for all transition inputs that are records.
    pub fn tags(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.transactions.tags()
    }

    /// Returns an iterator over the input IDs, for all transition inputs that are records.
    pub fn input_ids(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.transactions.input_ids()
    }

    /// Returns an iterator over the serial numbers, for all transition inputs that are records.
    pub fn serial_numbers(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.transactions.serial_numbers()
    }

    /// Returns an iterator over the output IDs, for all transition inputs that are records.
    pub fn output_ids(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.transactions.output_ids()
    }

    /// Returns an iterator over the commitments, for all transition outputs that are records.
    pub fn commitments(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.transactions.commitments()
    }

    /// Returns an iterator over the records, for all transition outputs that are records.
    pub fn records(&self) -> impl '_ + Iterator<Item = (&Field<N>, &Record<N, Ciphertext<N>>)> {
        self.transactions.records()
    }

    /// Returns an iterator over the nonces, for all transition outputs that are records.
    pub fn nonces(&self) -> impl '_ + Iterator<Item = &Group<N>> {
        self.transactions.nonces()
    }

    /// Returns an iterator over the transaction fees, for all transactions.
    pub fn transaction_fees(&self) -> impl '_ + Iterator<Item = Result<U64<N>>> {
        self.transactions.transaction_fees()
    }
}

impl<N: Network> Block<N> {
    /// Returns a consuming iterator over the transaction IDs, for all transactions in `self`.
    pub fn into_transaction_ids(self) -> impl Iterator<Item = N::TransactionID> {
        self.transactions.into_transaction_ids()
    }

    /// Returns a consuming iterator over all transactions in `self` that are accepted deploy transactions.
    pub fn into_deployments(self) -> impl Iterator<Item = ConfirmedTransaction<N>> {
        self.transactions.into_deployments()
    }

    /// Returns a consuming iterator over all transactions in `self` that are accepted execute transactions.
    pub fn into_executions(self) -> impl Iterator<Item = ConfirmedTransaction<N>> {
        self.transactions.into_executions()
    }

    /// Returns a consuming iterator over all transitions.
    pub fn into_transitions(self) -> impl Iterator<Item = Transition<N>> {
        self.transactions.into_transitions()
    }

    /// Returns a consuming iterator over the transition IDs, for all transitions.
    pub fn into_transition_ids(self) -> impl Iterator<Item = N::TransitionID> {
        self.transactions.into_transition_ids()
    }

    /// Returns a consuming iterator over the transition public keys, for all transactions.
    pub fn into_transition_public_keys(self) -> impl Iterator<Item = Group<N>> {
        self.transactions.into_transition_public_keys()
    }

    /// Returns a consuming iterator over the tags, for all transition inputs that are records.
    pub fn into_tags(self) -> impl Iterator<Item = Field<N>> {
        self.transactions.into_tags()
    }

    /// Returns a consuming iterator over the serial numbers, for all transition inputs that are records.
    pub fn into_serial_numbers(self) -> impl Iterator<Item = Field<N>> {
        self.transactions.into_serial_numbers()
    }

    /// Returns a consuming iterator over the commitments, for all transition outputs that are records.
    pub fn into_commitments(self) -> impl Iterator<Item = Field<N>> {
        self.transactions.into_commitments()
    }

    /// Returns a consuming iterator over the records, for all transition outputs that are records.
    pub fn into_records(self) -> impl Iterator<Item = (Field<N>, Record<N, Ciphertext<N>>)> {
        self.transactions.into_records()
    }

    /// Returns a consuming iterator over the nonces, for all transition outputs that are records.
    pub fn into_nonces(self) -> impl Iterator<Item = Group<N>> {
        self.transactions.into_nonces()
    }
}

#[cfg(test)]
pub mod test_helpers {
    use super::*;
    use console::account::{Address, PrivateKey};
    use ledger_query::Query;
    use ledger_store::{helpers::memory::BlockMemory, BlockStore};
    use synthesizer_process::Process;

    use once_cell::sync::OnceCell;

    type CurrentNetwork = console::network::Testnet3;
    type CurrentAleo = circuit::network::AleoV0;

    /// Samples a random genesis block.
    pub(crate) fn sample_genesis_block(rng: &mut TestRng) -> Block<CurrentNetwork> {
        // Sample the genesis block and components.
        let (block, _, _) = sample_genesis_block_and_components(rng);
        // Return the block.
        block
    }

    /// Samples a random genesis block and the transaction from the genesis block.
    pub(crate) fn sample_genesis_block_and_transaction(
        rng: &mut TestRng,
    ) -> (Block<CurrentNetwork>, Transaction<CurrentNetwork>) {
        // Sample the genesis block and components.
        let (block, transaction, _) = sample_genesis_block_and_components(rng);
        // Return the block and transaction.
        (block, transaction)
    }

    /// Samples a random genesis block, the transaction from the genesis block, and the genesis private key.
    pub(crate) fn sample_genesis_block_and_components(
        rng: &mut TestRng,
    ) -> (Block<CurrentNetwork>, Transaction<CurrentNetwork>, PrivateKey<CurrentNetwork>) {
        static INSTANCE: OnceCell<(Block<CurrentNetwork>, Transaction<CurrentNetwork>, PrivateKey<CurrentNetwork>)> =
            OnceCell::new();
        INSTANCE.get_or_init(|| sample_genesis_block_and_components_raw(rng)).clone()
    }

    /// Samples a random genesis block, the transaction from the genesis block, and the genesis private key.
    fn sample_genesis_block_and_components_raw(
        rng: &mut TestRng,
    ) -> (Block<CurrentNetwork>, Transaction<CurrentNetwork>, PrivateKey<CurrentNetwork>) {
        // Sample the genesis private key.
        let private_key = PrivateKey::new(rng).unwrap();
        let address = Address::<CurrentNetwork>::try_from(private_key).unwrap();

        // Prepare the locator.
        let locator = ("credits.aleo", "mint");
        // Prepare the amount for each call to the mint function.
        let amount = 100_000_000u64;
        // Prepare the function inputs.
        let inputs = [address.to_string(), format!("{amount}_u64")];

        // Initialize the process.
        let process = Process::load().unwrap();
        // Authorize the mint function.
        let authorization =
            process.authorize::<CurrentAleo, _>(&private_key, locator.0, locator.1, inputs.iter(), rng).unwrap();
        // Execute the mint function.
        let (_, mut trace) = process.execute::<CurrentAleo>(authorization).unwrap();

        // Initialize a new block store.
        let block_store = BlockStore::<CurrentNetwork, BlockMemory<_>>::open(None).unwrap();

        // Prepare the assignments.
        trace.prepare(Query::from(block_store)).unwrap();
        // Compute the proof and construct the execution.
        let execution = trace.prove_execution::<CurrentAleo, _>(locator.0, rng).unwrap();
        // Convert the execution.
        // Note: This is a testing-only hack to adhere to Rust's dependency cycle rules.
        let execution = Execution::from_str(&execution.to_string()).unwrap();

        // Construct the transaction.
        let transaction = Transaction::from_execution(execution, None).unwrap();
        // Prepare the confirmed transaction.
        let confirmed = ConfirmedTransaction::accepted_execute(0, transaction.clone(), vec![]).unwrap();
        // Prepare the transactions.
        let transactions = Transactions::from_iter([confirmed].into_iter());

        // Prepare the block header.
        let header = Header::genesis(&transactions).unwrap();
        // Prepare the previous block hash.
        let previous_hash = <CurrentNetwork as Network>::BlockHash::default();

        // Construct the block.
        let block = Block::new(&private_key, previous_hash, header, transactions, vec![], None, rng).unwrap();
        assert!(block.header().is_genesis(), "Failed to initialize a genesis block");
        // Return the block, transaction, and private key.
        (block, transaction, private_key)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use indexmap::IndexMap;

    #[test]
    fn test_find_transaction_for_transition_id() {
        let rng = &mut TestRng::default();

        let (block, transaction) = crate::test_helpers::sample_genesis_block_and_transaction(rng);
        let transactions = block.transactions();

        // Retrieve the transitions.
        let transitions = transaction.transitions().collect::<Vec<_>>();
        assert!(!transitions.is_empty());

        // Ensure the transaction is found.
        for transition in transitions {
            assert_eq!(block.find_transaction_for_transition_id(transition.id()), Some(&transaction));
            assert_eq!(transactions.find_transaction_for_transition_id(transition.id()), Some(&transaction));
        }

        // Ensure the transaction is not found.
        for _ in 0..10 {
            let transition_id = &rng.gen();
            assert_eq!(block.find_transaction_for_transition_id(transition_id), None);
            assert_eq!(transactions.find_transaction_for_transition_id(transition_id), None);
        }
    }

    #[test]
    fn test_find_transaction_for_commitment() {
        let rng = &mut TestRng::default();

        let (block, transaction) = crate::test_helpers::sample_genesis_block_and_transaction(rng);
        let transactions = block.transactions();

        // Retrieve the commitments.
        let commitments = transaction.commitments().collect::<Vec<_>>();
        assert!(!commitments.is_empty());

        // Ensure the commitments are found.
        for commitment in commitments {
            assert_eq!(block.find_transaction_for_commitment(commitment), Some(&transaction));
            assert_eq!(transactions.find_transaction_for_commitment(commitment), Some(&transaction));
        }

        // Ensure the commitments are not found.
        for _ in 0..10 {
            let commitment = &rng.gen();
            assert_eq!(block.find_transaction_for_commitment(commitment), None);
            assert_eq!(transactions.find_transaction_for_commitment(commitment), None);
        }
    }

    #[test]
    fn test_find_transition() {
        let rng = &mut TestRng::default();

        let (block, transaction) = crate::test_helpers::sample_genesis_block_and_transaction(rng);
        let transactions = block.transactions();

        // Retrieve the transitions.
        let transitions = transaction.transitions().collect::<Vec<_>>();
        assert!(!transitions.is_empty());

        // Ensure the transitions are found.
        for transition in transitions {
            assert_eq!(block.find_transition(transition.id()), Some(transition));
            assert_eq!(transactions.find_transition(transition.id()), Some(transition));
            assert_eq!(transaction.find_transition(transition.id()), Some(transition));
        }

        // Ensure the transitions are not found.
        for _ in 0..10 {
            let transition_id = &rng.gen();
            assert_eq!(block.find_transition(transition_id), None);
            assert_eq!(transactions.find_transition(transition_id), None);
            assert_eq!(transaction.find_transition(transition_id), None);
        }
    }

    #[test]
    fn test_find_transition_for_commitment() {
        let rng = &mut TestRng::default();

        let (block, transaction) = crate::test_helpers::sample_genesis_block_and_transaction(rng);
        let transactions = block.transactions();

        // Retrieve the transitions.
        let transitions = transaction.transitions().collect::<Vec<_>>();
        assert!(!transitions.is_empty());

        for transition in transitions {
            // Retrieve the commitments.
            let commitments = transition.commitments().collect::<Vec<_>>();
            assert!(!commitments.is_empty());

            // Ensure the commitments are found.
            for commitment in commitments {
                assert_eq!(block.find_transition_for_commitment(commitment), Some(transition));
                assert_eq!(transactions.find_transition_for_commitment(commitment), Some(transition));
                assert_eq!(transaction.find_transition_for_commitment(commitment), Some(transition));
            }
        }

        // Ensure the commitments are not found.
        for _ in 0..10 {
            let commitment = &rng.gen();
            assert_eq!(block.find_transition_for_commitment(commitment), None);
            assert_eq!(transactions.find_transition_for_commitment(commitment), None);
            assert_eq!(transaction.find_transition_for_commitment(commitment), None);
        }
    }

    #[test]
    fn test_find_record() {
        let rng = &mut TestRng::default();

        let (block, transaction) = crate::test_helpers::sample_genesis_block_and_transaction(rng);
        let transactions = block.transactions();

        // Retrieve the records.
        let records = transaction.records().collect::<IndexMap<_, _>>();
        assert!(!records.is_empty());

        // Ensure the records are found.
        for (commitment, record) in records {
            assert_eq!(block.find_record(commitment), Some(record));
            assert_eq!(transactions.find_record(commitment), Some(record));
            assert_eq!(transaction.find_record(commitment), Some(record));
        }

        // Ensure the records are not found.
        for _ in 0..10 {
            let commitment = &rng.gen();
            assert_eq!(block.find_record(commitment), None);
            assert_eq!(transactions.find_record(commitment), None);
            assert_eq!(transaction.find_record(commitment), None);
        }
    }
}
