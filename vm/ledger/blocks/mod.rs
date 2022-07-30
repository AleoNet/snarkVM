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

use crate::{
    compiler::Transition,
    console::{
        collections::merkle_tree::MerklePath,
        network::{prelude::*, BHPMerkleTree},
        types::{Field, Group},
    },
    ledger::{
        map::{memory_map::MemoryMap, Map, MapReader},
        state_path::StatePath,
        Block,
        Header,
        HeaderLeaf,
        Transaction,
        Transactions,
    },
    parameters::testnet3::GenesisBytes,
};

use anyhow::{anyhow, Result};
use time::OffsetDateTime;

/// The depth of the Merkle tree for the blocks.
const BLOCKS_DEPTH: u8 = 32;

/// The Merkle tree for the block state.
pub type BlockTree<N> = BHPMerkleTree<N, BLOCKS_DEPTH>;
/// The Merkle path for the state tree blocks.
pub type BlockPath<N> = MerklePath<N, BLOCKS_DEPTH>;

#[derive(Clone)]
pub struct Blocks<N: Network> {
    /// The current block height.
    pub(super) current_height: u32,
    /// The current block hash.
    pub(super) current_hash: N::BlockHash,
    /// The current block tree.
    pub(super) block_tree: BlockTree<N>,
    /// The chain of previous block hashes.
    pub(super) previous_hashes: MemoryMap<u32, N::BlockHash>,
    /// The chain of block headers.
    pub(super) headers: MemoryMap<u32, Header<N>>,
    /// The chain of block transactions.
    pub(super) transactions: MemoryMap<u32, Transactions<N>>,
}

impl<N: Network> Blocks<N> {
    /// Initializes a new instance of `Blocks` with the genesis block.
    pub fn new() -> Result<Self> {
        // Load the genesis block.
        let genesis = Block::<N>::from_bytes_le(GenesisBytes::load_bytes())?;
        // Construct the blocks.
        Ok(Self {
            current_height: genesis.height(),
            current_hash: genesis.hash(),
            block_tree: N::merkle_tree_bhp(&[genesis.hash().to_bits_le()])?,
            previous_hashes: [(genesis.height(), genesis.previous_hash())].into_iter().collect(),
            headers: [(genesis.height(), *genesis.header())].into_iter().collect(),
            transactions: [(genesis.height(), genesis.transactions().clone())].into_iter().collect(),
        })
    }
}

impl<N: Network> Blocks<N> {
    /// Returns the latest state root.
    pub fn latest_state_root(&self) -> &Field<N> {
        self.block_tree.root()
    }

    /// Returns the latest block.
    pub fn latest_block(&self) -> Result<Block<N>> {
        self.get_block(self.current_height)
    }

    /// Returns the latest block height.
    pub fn latest_height(&self) -> u32 {
        self.current_height
    }

    /// Returns the latest block hash.
    pub fn latest_hash(&self) -> N::BlockHash {
        self.current_hash
    }

    /// Returns the latest round number.
    pub fn latest_round(&self) -> Result<u64> {
        Ok(self.get_header(self.current_height)?.round())
    }

    /// Returns the latest block coinbase target.
    pub fn latest_coinbase_target(&self) -> Result<u64> {
        Ok(self.get_header(self.current_height)?.coinbase_target())
    }

    /// Returns the latest block proof target.
    pub fn latest_proof_target(&self) -> Result<u64> {
        Ok(self.get_header(self.current_height)?.proof_target())
    }

    /// Returns the latest block timestamp.
    pub fn latest_timestamp(&self) -> Result<i64> {
        Ok(self.get_header(self.current_height)?.timestamp())
    }

    /// Returns the latest block transactions.
    pub fn latest_transactions(&self) -> Result<&Transactions<N>> {
        self.get_transactions(self.current_height)
    }
}

impl<N: Network> Blocks<N> {
    /// Returns the block for the given block height.
    pub fn get_block(&self, height: u32) -> Result<Block<N>> {
        Block::from(self.get_previous_hash(height)?, *self.get_header(height)?, self.get_transactions(height)?.clone())
    }

    /// Returns the block hash for the given block height.
    pub fn get_hash(&self, height: u32) -> Result<N::BlockHash> {
        match height.cmp(&self.current_height) {
            Ordering::Equal => Ok(self.current_hash),
            Ordering::Less => match self.previous_hashes.get(&(height + 1))? {
                Some(block_hash) => Ok(*block_hash),
                None => bail!("Missing block hash for block {height}"),
            },
            Ordering::Greater => bail!("Block {height} (given) is greater than the current height"),
        }
    }

    /// Returns the previous block hash for the given block height.
    pub fn get_previous_hash(&self, height: u32) -> Result<N::BlockHash> {
        match self.previous_hashes.get(&height)? {
            Some(previous_hash) => Ok(*previous_hash),
            None => bail!("Missing previous block hash for block {height}"),
        }
    }

    /// Returns the block header for the given block height.
    pub fn get_header(&self, height: u32) -> Result<&Header<N>> {
        match self.headers.get(&height)? {
            Some(header) => Ok(header),
            None => bail!("Missing block header for block {height}"),
        }
    }

    /// Returns the block transactions for the given block height.
    pub fn get_transactions(&self, height: u32) -> Result<&Transactions<N>> {
        match self.transactions.get(&height)? {
            Some(transactions) => Ok(transactions),
            None => bail!("Missing block transactions for block {height}"),
        }
    }
}

impl<N: Network> Blocks<N> {
    /// Returns an iterator over all transactions.
    pub fn transactions(&self) -> impl '_ + Iterator<Item = &Transaction<N>> {
        self.transactions.values().flat_map(|transactions| transactions.values())
    }

    /// Returns an iterator over the transaction IDs, for all transactions in `self`.
    pub fn transaction_ids(&self) -> impl '_ + Iterator<Item = &N::TransactionID> {
        self.transactions.values().flat_map(Transactions::transaction_ids)
    }

    /// Returns an iterator over all executed transitions.
    pub fn transitions(&self) -> impl '_ + Iterator<Item = &Transition<N>> {
        self.transactions.values().flat_map(Transactions::transitions)
    }

    /// Returns an iterator over the transition IDs, for all executed transitions.
    pub fn transition_ids(&self) -> impl '_ + Iterator<Item = &N::TransitionID> {
        self.transactions.values().flat_map(Transactions::transition_ids)
    }

    /// Returns an iterator over the transition public keys, for all executed transactions.
    pub fn transition_public_keys(&self) -> impl '_ + Iterator<Item = &Group<N>> {
        self.transactions.values().flat_map(Transactions::transition_public_keys)
    }

    /// Returns an iterator over the serial numbers, for all executed transition inputs that are records.
    pub fn serial_numbers(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.transactions.values().flat_map(Transactions::serial_numbers)
    }

    /// Returns an iterator over the commitments, for all executed transition outputs that are records.
    pub fn commitments(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.transactions.values().flat_map(Transactions::commitments)
    }

    /// Returns an iterator over the nonces, for all executed transition outputs that are records.
    pub fn nonces(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.transactions.values().flat_map(Transactions::nonces)
    }
}

impl<N: Network> Blocks<N> {
    /// Returns `true` if the given state root exists.
    pub fn contains_state_root(&self, state_root: &Field<N>) -> bool {
        state_root == self.latest_state_root()
            || self.headers.values().map(Header::previous_state_root).any(|root| root == state_root)
    }

    /// Returns `true` if the given block height exists.
    pub fn contains_height(&self, height: u32) -> Result<bool> {
        self.previous_hashes
            .contains_key(&height)
            .or_else(|_| self.headers.contains_key(&height))
            .or_else(|_| self.transactions.contains_key(&height))
    }

    /// Returns `true` if the given block hash exists.
    pub fn contains_block_hash(&self, block_hash: &N::BlockHash) -> bool {
        self.current_hash == *block_hash || self.previous_hashes.values().any(|hash| *hash == *block_hash)
    }

    /// Returns `true` if the given transaction exists.
    pub fn contains_transaction(&self, transaction: &Transaction<N>) -> bool {
        self.transaction_ids().contains(&transaction.id())
    }

    /// Returns `true` if the given transaction ID exists.
    pub fn contains_transaction_id(&self, transaction_id: &N::TransactionID) -> bool {
        self.transaction_ids().contains(transaction_id)
    }

    /// Returns `true` if the given transition exists.
    pub fn contains_transition(&self, transition: &Transition<N>) -> bool {
        self.transition_ids().contains(transition.id())
    }

    /// Returns `true` if the given transition ID exists.
    pub fn contains_transition_id(&self, transition_id: &N::TransitionID) -> bool {
        self.transition_ids().contains(transition_id)
    }

    /// Returns `true` if the given transition public key exists.
    pub fn contains_transition_public_keys(&self, tpk: &Group<N>) -> bool {
        self.transition_public_keys().contains(tpk)
    }

    /// Returns `true` if the given serial number exists.
    pub fn contains_serial_number(&self, serial_number: &Field<N>) -> bool {
        self.serial_numbers().contains(serial_number)
    }

    /// Returns `true` if the given commitment exists.
    pub fn contains_commitment(&self, commitment: &Field<N>) -> bool {
        self.commitments().contains(commitment)
    }

    /// Returns `true` if the given nonce exists.
    pub fn contains_nonce(&self, commitment: &Field<N>) -> bool {
        self.nonces().contains(commitment)
    }
}

impl<N: Network> Blocks<N> {
    /// Returns a proposal block constructed with the transactions in the mempool.
    pub fn propose_block(&self, transactions: Transactions<N>) -> Result<Block<N>> {
        // Fetch the latest block hash
        let latest_block_hash = self.latest_hash();

        // Construct the block header.
        let latest_state_root = self.latest_state_root();
        let transactions_root = transactions.to_root()?;
        let network = N::ID;
        let height = self.latest_height() + 1;
        // TODO (raychu86): Establish the correct round, coinbase target, and proof target.
        let round = 1;
        let coinbase_target = 0;
        let proof_target = 0;
        let timestamp = OffsetDateTime::now_utc().unix_timestamp();
        let header = Header::from(
            *latest_state_root,
            transactions_root,
            network,
            height,
            round,
            coinbase_target,
            proof_target,
            timestamp,
        )?;

        // Construct the new block.
        let block = Block::from(latest_block_hash, header, transactions)?;

        // TODO (raychu86): Ensure the block is valid.
        // // Ensure the block itself is valid.
        // if !block.is_valid(vm) {
        //     return Err(anyhow!("The proposed block is invalid"));
        // }

        Ok(block)
    }

    /// Adds the given block as the next block in the chain.
    pub fn add_next(&mut self, block: &Block<N>) -> Result<()> {
        // TODO (raychu86): Validate the block using a valid VM.
        // // Ensure the block itself is valid.
        // if !block.is_valid(vm) {
        //     return Err(anyhow!("The given block is invalid"));
        // }

        // Ensure the next block height is correct.
        let height = block.header().height();
        if self.latest_height() != 0 && self.latest_height() + 1 != height {
            return Err(anyhow!("The given block has an incorrect block height"));
        }

        // Ensure the block height does not already exist.
        if self.contains_height(height)? {
            return Err(anyhow!("The given block height already exists in the ledger"));
        }

        // Ensure the previous block hash is correct.
        if self.current_hash != block.previous_hash() {
            return Err(anyhow!("The given block has an incorrect previous block hash"));
        }

        // Ensure the block hash does not already exist.
        let block_hash = block.hash();
        if self.contains_block_hash(&block_hash) {
            return Err(anyhow!("The given block hash already exists in the ledger"));
        }

        // TODO (raychu86): Ensure the next block timestamp is the median of proposed blocks.

        // Ensure the next block timestamp is after the current block timestamp.
        if self.contains_height(0)? {
            let current_block = self.latest_block()?;
            if block.header().timestamp() <= current_block.header().timestamp() {
                return Err(anyhow!("The given block timestamp is before the current timestamp"));
            }
        }

        // TODO (raychu86): Add proof and coinbase target verification.

        for (_, transaction) in block.transactions().iter() {
            // Ensure the transaction in the block do not already exist.
            if self.contains_transaction(transaction) {
                return Err(anyhow!("The given block has a duplicate transaction in the ledger"));
            }
            // TODO (raychu86): Ensure the transaction in the block references a valid past or current ledger root.
            // if !self.contains_state_root(&transaction.state_root()) {
            //     return Err(anyhow!(
            //         "The given transaction references a non-existent state root {}",
            //         &transaction.state_root()
            //     ));
            // }
        }

        // Ensure the ledger does not already contain a given serial numbers.
        for serial_number in block.transactions().serial_numbers() {
            if self.contains_serial_number(serial_number) {
                return Err(anyhow!("Serial number already exists in the ledger"));
            }
        }

        // Ensure the ledger does not already contain a given commitments.
        for commitment in block.transactions().commitments() {
            if self.contains_commitment(commitment) {
                return Err(anyhow!("Commitment already exists in the ledger"));
            }
        }

        // Add the block to the ledger. This code section executes atomically.
        {
            let mut blocks = self.clone();

            blocks.current_height = height;
            blocks.current_hash = block_hash;
            blocks.block_tree.append(&[block.hash().to_bits_le()])?;
            blocks.previous_hashes.insert::<u32>(height, block.previous_hash())?;
            blocks.headers.insert::<u32>(height, *block.header())?;
            blocks.transactions.insert::<u32>(height, block.transactions().clone())?;

            *self = blocks;
        }

        Ok(())
    }

    /// Returns the ledger tree.
    pub fn to_ledger_tree(&self) -> &BlockTree<N> {
        &self.block_tree
    }

    ///
    /// Returns a state path for the given commitment.
    ///
    pub fn to_state_path(&self, commitment: &Field<N>) -> Result<StatePath<N>> {
        // Find the transaction that contains the record commitment.
        let transaction = self
            .transactions
            .iter()
            .flat_map(|(_, transactions)| &**transactions)
            .filter(|(_, transaction)| transaction.commitments().contains(&commitment))
            .collect::<Vec<_>>();

        if transaction.len() != 1 {
            return Err(anyhow!("Multiple transactions associated with commitment {}", commitment.to_string()));
        }

        let (transaction_id, transaction) = transaction[0];

        // Find the block height that contains the record transaction id.
        let block_height = self
            .transactions
            .iter()
            .filter_map(|(block_height, transactions)| match transactions.transaction_ids().contains(&transaction_id) {
                true => Some(block_height),
                false => None,
            })
            .collect::<Vec<_>>();

        if block_height.len() != 1 {
            return Err(anyhow!(
                "Multiple block heights associated with transaction id {}",
                transaction_id.to_string()
            ));
        }

        let block_height = *block_height[0];
        let block_header = self.get_header(block_height)?;

        // Find the transition that contains the record commitment.
        let transition = transaction
            .transitions()
            .filter(|transition| transition.commitments().contains(&commitment))
            .collect::<Vec<_>>();

        if transition.len() != 1 {
            return Err(anyhow!("Multiple transitions associated with commitment {}", commitment.to_string()));
        }

        let transition = transition[0];
        let transition_id = transition.id();

        // Construct the transition path and transaction leaf.
        let transition_leaf = transition.to_leaf(commitment, false)?;
        let transition_path = transition.to_path(&transition_leaf)?;

        // Construct the transaction path and transaction leaf.
        let transaction_leaf = transaction.to_leaf(transition_id)?;
        let transaction_path = transaction.to_path(&transaction_leaf)?;

        // Construct the transactions path.
        let transactions = self.get_transactions(block_height)?;
        let transaction_index = transactions.iter().position(|(id, _)| id == transaction_id).unwrap();
        let transactions_path = transactions.to_path(transaction_index, **transaction_id)?;

        // Construct the block header path.
        let header_root = block_header.to_root()?;
        let header_leaf = HeaderLeaf::<N>::new(1, *block_header.transactions_root());
        let header_path = block_header.to_path(&header_leaf)?;

        // Construct the block path.
        let latest_block_height = self.latest_height();
        let latest_block_hash = self.latest_hash();
        let previous_block_hash = self.get_previous_hash(latest_block_height)?;

        // Construct the state root and block path.
        let state_root = *self.latest_state_root();
        let block_path = self.block_tree.prove(latest_block_height as usize, &latest_block_hash.to_bits_le())?;

        StatePath::new(
            state_root.into(),
            block_path,
            latest_block_hash,
            previous_block_hash,
            header_root,
            header_path,
            header_leaf,
            transactions_path,
            *transaction_id,
            transaction_path,
            transaction_leaf,
            transition_path,
            transition_leaf,
        )
    }

    /// Returns the expected coinbase target given the previous block and expected next block details.
    pub fn compute_coinbase_target(_anchor_block_header: &Header<N>, _block_timestamp: i64, _block_height: u32) -> u64 {
        unimplemented!()
    }

    /// Returns the expected proof target given the previous block and expected next block details.
    pub fn compute_proof_target(_anchor_block_header: &Header<N>, _block_timestamp: i64, _block_height: u32) -> u64 {
        unimplemented!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{console::network::Testnet3, test_helpers::sample_execution_transaction};

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_get_block() {
        // Load the genesis block.
        let genesis = Block::from_bytes_le(GenesisBytes::load_bytes()).unwrap();

        // Initialize a new ledger.
        let blocks = Blocks::<CurrentNetwork>::new().unwrap();
        // Retrieve the genesis block.
        let candidate = blocks.get_block(0).unwrap();
        // Ensure the genesis block matches.
        assert_eq!(genesis, candidate);
    }

    #[test]
    fn test_deploy() {
        let _blocks = Blocks::<CurrentNetwork>::new().unwrap();
    }

    #[test]
    fn test_state_path() {
        // Initialize the ledger with the genesis block.
        let blocks = Blocks::<CurrentNetwork>::new().unwrap();
        // Retrieve the genesis block.
        let genesis = blocks.get_block(0).unwrap();

        // Construct the state path.
        let commitments = genesis.transactions().commitments().collect::<Vec<_>>();
        let commitment = commitments[0];

        let _state_path = blocks.to_state_path(commitment).unwrap();
    }

    #[test]
    fn test_new_blocks() {
        // Initialize the ledger with the genesis block.
        let mut blocks = Blocks::<CurrentNetwork>::new().unwrap();
        // Retrieve the genesis block.
        let genesis = blocks.get_block(0).unwrap();
        assert_eq!(blocks.latest_height(), 0);
        assert_eq!(blocks.latest_hash(), genesis.hash());

        // Construct a new block.
        let new_transaction = sample_execution_transaction();
        let transactions = Transactions::from(&[new_transaction]).unwrap();

        let new_block = blocks.propose_block(transactions).unwrap();
        blocks.add_next(&new_block).unwrap();

        assert_eq!(blocks.latest_height(), 1);
        assert_eq!(blocks.latest_hash(), new_block.hash());
    }
}
