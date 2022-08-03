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

mod block;
pub use block::*;

mod map;
pub use map::*;

mod state_path;
pub use state_path::*;

mod transaction;
pub use transaction::*;

mod transition;
pub use transition::*;

mod vm;
pub use vm::*;

mod contains;
mod get;
mod iterators;
mod latest;

use crate::{
    ledger::Origin,
    process::{Deployment, Execution},
};
use console::{
    account::{PrivateKey, Signature, ViewKey},
    collections::merkle_tree::MerklePath,
    network::{prelude::*, BHPMerkleTree},
    program::{Identifier, Plaintext, ProgramID, Record},
    types::{Field, Group},
};
use snarkvm_parameters::testnet3::GenesisBytes;

use anyhow::Result;
use indexmap::IndexMap;
use time::OffsetDateTime;

/// The depth of the Merkle tree for the blocks.
const BLOCKS_DEPTH: u8 = 32;

/// The Merkle tree for the block state.
pub type BlockTree<N> = BHPMerkleTree<N, BLOCKS_DEPTH>;
/// The Merkle path for the state tree blocks.
pub type BlockPath<N> = MerklePath<N, BLOCKS_DEPTH>;

pub enum OutputRecordsFilter<N: Network> {
    /// Returns all output records associated with the account.
    All,
    /// Returns only output records associated with the account that are **spent**.
    Spent(PrivateKey<N>),
    /// Returns only output records associated with the account that are **not spent**.
    Unspent(PrivateKey<N>),
}

#[derive(Clone)]
pub struct Ledger<
    N: Network,
    PreviousHashesMap: for<'a> Map<'a, u32, N::BlockHash>,
    HeadersMap: for<'a> Map<'a, u32, Header<N>>,
    TransactionsMap: for<'a> Map<'a, u32, Transactions<N>>,
    SignatureMap: for<'a> Map<'a, u32, Signature<N>>,
> {
    /// The current block hash.
    current_hash: N::BlockHash,
    /// The current block height.
    current_height: u32,
    /// The current round number.
    current_round: u64,
    /// The current block tree.
    block_tree: BlockTree<N>,
    /// The map of previous block hashes.
    previous_hashes: PreviousHashesMap,
    /// The map of block headers.
    headers: HeadersMap,
    /// The map of block transactions.
    transactions: TransactionsMap,
    /// The map of block signatures.
    signatures: SignatureMap,
    /// The memory pool of unconfirmed transactions.
    memory_pool: IndexMap<N::TransactionID, Transaction<N>>,
    /// The VM state.
    vm: VM<N>,
    // /// The mapping of program IDs to their global state.
    // states: MemoryMap<ProgramID<N>, IndexMap<Identifier<N>, Plaintext<N>>>,
}

impl<
    N: Network,
    PreviousHashesMap: for<'a> Map<'a, u32, N::BlockHash>,
    HeadersMap: for<'a> Map<'a, u32, Header<N>>,
    TransactionsMap: for<'a> Map<'a, u32, Transactions<N>>,
    SignatureMap: for<'a> Map<'a, u32, Signature<N>>,
> Ledger<N, PreviousHashesMap, HeadersMap, TransactionsMap, SignatureMap>
{
    /// Initializes a new instance of `Blocks` with the genesis block.
    pub fn new() -> Result<Self> {
        // Load the genesis block.
        let genesis = Block::<N>::from_bytes_le(GenesisBytes::load_bytes())?;

        // Load the VM with deployment functions.
        let mut vm = VM::<N>::new()?;
        for deployment_transaction in
            genesis.transactions().values().filter(|transaction| matches!(transaction, Transaction::Deploy(..)))
        {
            vm.on_deploy(deployment_transaction)?;
        }

        // Construct the blocks.
        Ok(Self {
            current_hash: genesis.hash(),
            current_height: genesis.height(),
            current_round: genesis.round(),
            block_tree: N::merkle_tree_bhp(&[genesis.hash().to_bits_le()])?,
            previous_hashes: [(genesis.height(), genesis.previous_hash())].into_iter().collect(),
            headers: [(genesis.height(), *genesis.header())].into_iter().collect(),
            transactions: [(genesis.height(), genesis.transactions().clone())].into_iter().collect(),
            signatures: [(genesis.height(), *genesis.signature())].into_iter().collect(),
            vm,
            memory_pool: Default::default(),
        })
    }

    /// Returns the VM.
    pub fn vm(&self) -> &VM<N> {
        &self.vm
    }

    /// Appends the given transaction to the memory pool.
    pub fn add_to_memory_pool(&mut self, transaction: Transaction<N>) -> Result<()> {
        // Ensure the transaction does not already exist.
        if self.memory_pool.contains_key(&transaction.id()) {
            bail!("Transaction '{}' already exists in the memory pool.", transaction.id());
        }

        // Ensure the ledger does not already contain a given transition public keys.
        for tpk in transaction.transition_public_keys() {
            if self.contains_transition_public_key(tpk) {
                bail!("Transition public key '{tpk}' already exists in the ledger")
            }
        }

        // Ensure the ledger does not already contain a given serial numbers.
        for serial_number in transaction.serial_numbers() {
            if self.contains_serial_number(serial_number) {
                bail!("Serial number '{serial_number}' already exists in the ledger")
            }
        }

        // Ensure the ledger does not already contain a given commitments.
        for commitment in transaction.commitments() {
            if self.contains_commitment(commitment) {
                bail!("Commitment '{commitment}' already exists in the ledger")
            }
        }

        // Ensure the ledger does not already contain a given nonces.
        for nonce in transaction.nonces() {
            if self.contains_nonce(nonce) {
                bail!("Nonce '{nonce}' already exists in the ledger")
            }
        }

        // Insert the transaction to the memory pool.
        self.memory_pool.insert(transaction.id(), transaction);
        Ok(())
    }

    /// Returns a candidate for the next block in the ledger.
    pub fn propose_next_block<R: Rng + CryptoRng>(&self, private_key: &PrivateKey<N>, rng: &mut R) -> Result<Block<N>> {
        // Construct the transactions for the block.
        let transactions = self.memory_pool.values().collect::<Transactions<N>>();

        // Fetch the latest block and state root.
        let block = self.latest_block()?;
        let state_root = self.latest_state_root();

        // TODO (raychu86): Establish the correct round, coinbase target, and proof target.
        let round = block.round() + 1;
        let coinbase_target = u64::MAX;
        let proof_target = u64::MAX;

        // Construct the certificate.
        let certificate = Metadata::new(
            N::ID,
            round,
            block.height() + 1,
            coinbase_target,
            proof_target,
            OffsetDateTime::now_utc().unix_timestamp(),
        )?;

        // Construct the header.
        let header = Header::from(*state_root, transactions.to_root()?, certificate)?;

        // Construct the new block.
        let block = Block::new(private_key, block.hash(), header, transactions, rng)?;

        // TODO (raychu86): Ensure the block is valid.
        // // Ensure the block itself is valid.
        // if !block.is_valid(vm) {
        //     bail!("The proposed block is invalid"));
        // }

        Ok(block)
    }

    /// Checks the given block is valid next block.
    pub fn check_next_block(&self, block: &Block<N>) -> Result<()> {
        // TODO (raychu86): Ensure the signature validation check passes.
        // // Ensure the block itself is valid.
        // if !block.verify(&self.vm) {
        //     bail!("The given block is invalid")
        // }

        // Ensure the previous block hash is correct.
        if self.current_hash != block.previous_hash() {
            bail!("The given block has an incorrect previous block hash")
        }

        // Ensure the block hash does not already exist.
        if self.contains_block_hash(&block.hash()) {
            bail!("Block hash '{}' already exists in the ledger", block.hash())
        }

        // Ensure the next block height is correct.
        if self.latest_height() != 0 && self.latest_height() + 1 != block.height() {
            bail!("The given block has an incorrect block height")
        }

        // Ensure the block height does not already exist.
        if self.contains_height(block.height())? {
            bail!("Block height '{}' already exists in the ledger", block.height())
        }

        // TODO (raychu86): Ensure the next round number includes timeouts.
        // Ensure the next round is correct.
        if self.latest_round() != 0 && self.latest_round() + 1 /*+ block.number_of_aborts()*/ != block.round() {
            bail!("The given block has an incorrect round number")
        }

        // TODO (raychu86): Ensure the next block timestamp is the median of proposed blocks.

        // Ensure the next block timestamp is after the current block timestamp.
        if block.header().timestamp() <= self.latest_block()?.header().timestamp() {
            bail!("The given block timestamp is before the current timestamp")
        }

        // TODO (raychu86): Add proof and coinbase target verification.

        for transaction_id in block.transaction_ids() {
            // Ensure the transaction in the block do not already exist.
            if self.contains_transaction_id(transaction_id) {
                bail!("Transaction '{transaction_id}' already exists in the ledger")
            }
        }

        // TODO (raychu86): Ensure the transaction in the block references a valid past or current ledger root.
        // if !self.contains_state_root(&transaction.state_root()) {
        //     bail!(
        //         "The given transaction references a non-existent state root {}",
        //         &transaction.state_root()
        //     ));
        // }

        // Ensure that the origin are valid.
        for origin in block.transitions().flat_map(Transition::origins) {
            match origin {
                // Check that the commitment exists in the ledger.
                Origin::Commitment(commitment) => {
                    if !self.contains_commitment(commitment) {
                        bail!("The given transaction references a non-existent commitment {}", &commitment)
                    }
                }
                // TODO (raychu86): Ensure that the state root exists in the ledger.
                // Check that the state root is an existing state root.
                Origin::StateRoot(_state_root) => {
                    bail!("State roots are currently not supported (yet)")
                }
            }
        }

        // Ensure the ledger does not already contain a given transition public keys.
        for tpk in block.transition_public_keys() {
            if self.contains_transition_public_key(tpk) {
                bail!("Transition public key '{tpk}' already exists in the ledger")
            }
        }

        // Ensure the ledger does not already contain a given serial numbers.
        for serial_number in block.serial_numbers() {
            if self.contains_serial_number(serial_number) {
                bail!("Serial number '{serial_number}' already exists in the ledger")
            }
        }

        // Ensure the ledger does not already contain a given commitments.
        for commitment in block.commitments() {
            if self.contains_commitment(commitment) {
                bail!("Commitment '{commitment}' already exists in the ledger")
            }
        }

        // Ensure the ledger does not already contain a given nonces.
        for nonce in block.nonces() {
            if self.contains_nonce(nonce) {
                bail!("Nonce '{nonce}' already exists in the ledger")
            }
        }

        let latest_height = self.latest_height();
        let credits_program_id = ProgramID::from_str("credits.aleo")?;
        let credits_genesis = Identifier::from_str("genesis")?;

        for transition in block.transitions() {
            if latest_height > 0 {
                // Ensure the genesis function is not called.
                if *transition.program_id() == credits_program_id && *transition.function_name() == credits_genesis {
                    bail!("The genesis function cannot be called.")
                }
                // Ensure the transition fee is not negative.
                if *transition.fee() < 0i64 {
                    bail!("The transition fee cannot be negative.")
                }
            }
        }

        Ok(())
    }

    /// Adds the given block as the next block in the chain.
    pub fn add_next_block(&mut self, block: &Block<N>) -> Result<()> {
        // Ensure the given block is a valid next block.
        self.check_next_block(block)?;

        /* ATOMIC CODE SECTION */

        // Add the block to the ledger. This code section executes atomically.
        {
            let mut ledger = self.clone();

            // Update the blocks.
            ledger.current_hash = block.hash();
            ledger.current_height = block.height();
            ledger.current_round = block.round();
            ledger.block_tree.append(&[block.hash().to_bits_le()])?;
            ledger.previous_hashes.insert(block.height(), block.previous_hash())?;
            ledger.headers.insert(block.height(), *block.header())?;
            ledger.transactions.insert(block.height(), block.transactions().clone())?;
            ledger.signatures.insert(block.height(), *block.signature())?;

            // TODO (howardwu): This logic was introduced without being atomic. Split into check on deploy first in VM.
            // // Load the VM with deployment functions in the block.
            // for deployment_transaction in
            //     block.transactions().values().filter(|transaction| matches!(transaction, Transaction::Deploy(..)))
            // {
            //     self.vm.on_deploy(deployment_transaction)?;
            // }

            // Clear the memory pool of these transactions.
            for transaction_id in block.transaction_ids() {
                ledger.memory_pool.remove(transaction_id);
            }

            *self = ledger;
        }

        Ok(())
    }

    /// Returns the block tree.
    pub fn to_block_tree(&self) -> &BlockTree<N> {
        &self.block_tree
    }

    /// Returns a state path for the given commitment.
    pub fn to_state_path(&self, commitment: &Field<N>) -> Result<StatePath<N>> {
        // Find the transaction that contains the record commitment.
        let transaction = self
            .transactions
            .iter()
            .filter(|(_, transactions)| transactions.commitments().contains(&commitment))
            .map(|(_, transactions)| transactions.into_owned())
            .flat_map(|transactions| transactions.into_inner())
            .collect::<Vec<(N::TransactionID, Transaction<N>)>>();

        if transaction.len() != 1 {
            bail!("Multiple transactions associated with commitment {}", commitment.to_string())
        }

        let (transaction_id, transaction) = &transaction[0];

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
            bail!("Multiple block heights associated with transaction id {}", transaction_id.to_string())
        }

        let block_height = *block_height[0];
        let block_header = self.get_header(block_height)?;

        // Find the transition that contains the record commitment.
        let transition = transaction
            .transitions()
            .filter(|transition| transition.commitments().contains(&commitment))
            .collect::<Vec<_>>();

        if transition.len() != 1 {
            bail!("Multiple transitions associated with commitment {}", commitment.to_string())
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
pub(crate) mod test_helpers {
    use super::*;
    use crate::ledger::memory_map::MemoryMap;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;
    pub(crate) type CurrentLedger = Ledger<
        CurrentNetwork,
        MemoryMap<u32, <CurrentNetwork as Network>::BlockHash>,
        MemoryMap<u32, Header<CurrentNetwork>>,
        MemoryMap<u32, Transactions<CurrentNetwork>>,
        MemoryMap<u32, Signature<CurrentNetwork>>,
    >;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ledger::{
        test_helpers::CurrentLedger,
        vm::test_helpers::{sample_deployment_transaction, sample_execution_transaction},
    };
    use console::network::Testnet3;
    use snarkvm_utilities::test_crypto_rng;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_state_path() {
        // Initialize the ledger with the genesis block.
        let ledger = CurrentLedger::new().unwrap();
        // Retrieve the genesis block.
        let genesis = ledger.get_block(0).unwrap();

        // Construct the state path.
        let commitments = genesis.transactions().commitments().collect::<Vec<_>>();
        let commitment = commitments[0];

        let _state_path = ledger.to_state_path(commitment).unwrap();
    }

    #[test]
    fn test_next_block() {
        let rng = &mut test_crypto_rng();

        // Sample a private key.
        let private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();

        // Initialize the ledger with the genesis block.
        let mut ledger = CurrentLedger::new().unwrap();

        // Retrieve the genesis block.
        let genesis = ledger.get_block(0).unwrap();
        assert_eq!(ledger.latest_height(), 0);
        assert_eq!(ledger.latest_hash(), genesis.hash());

        // Add a transaction to the memory pool.
        let transaction = sample_execution_transaction();
        ledger.add_to_memory_pool(transaction).unwrap();

        // Propose the next block.
        let next_block = ledger.propose_next_block(&private_key, rng).unwrap();

        // Construct a next block.
        ledger.add_next_block(&next_block).unwrap();

        assert_eq!(ledger.latest_height(), 1);
        assert_eq!(ledger.latest_hash(), next_block.hash());
    }

    #[test]
    fn test_ledger_vm() {
        let rng = &mut test_crypto_rng();

        // Sample a private key.
        let private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();

        // Initialize the ledger with the genesis block.
        let mut ledger = CurrentLedger::new().unwrap();

        // Add a transaction to the memory pool.
        let deployment_transaction = sample_deployment_transaction();
        ledger.add_to_memory_pool(deployment_transaction.clone()).unwrap();

        // Propose the next block.
        let next_block = ledger.propose_next_block(&private_key, rng).unwrap();

        // Construct a next block.
        ledger.add_next_block(&next_block).unwrap();

        // Ensure that the VM can't redeploy the same program.
        assert!(ledger.vm.on_deploy(&deployment_transaction).is_err());
    }
}
