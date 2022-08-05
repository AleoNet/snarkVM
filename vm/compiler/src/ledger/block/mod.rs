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

mod header;
pub use header::*;

mod transactions;
pub use transactions::*;

mod bytes;
mod genesis;
mod serialize;
mod string;

use crate::{
    ledger::{vm::VM, Origin, Transaction, Transition},
    process::{Deployment, Execution},
};
use console::{
    account::{Address, PrivateKey, Signature},
    network::prelude::*,
    program::{Identifier, ProgramID, Value},
    types::{Field, Group},
};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

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
    /// The signature for this block.
    signature: Signature<N>,
}

impl<N: Network> Block<N> {
    /// Initializes a new block from a given previous hash, header, and transactions list.
    pub fn new<R: Rng + CryptoRng>(
        private_key: &PrivateKey<N>,
        previous_hash: N::BlockHash,
        header: Header<N>,
        transactions: Transactions<N>,
        rng: &mut R,
    ) -> Result<Self> {
        // Ensure the block is not empty.
        ensure!(!transactions.is_empty(), "Cannot create block with no transactions");
        // Compute the block hash.
        let block_hash = N::hash_bhp1024(&[previous_hash.to_bits_le(), header.to_root()?.to_bits_le()].concat())?;
        // Sign the block hash.
        let signature = private_key.sign(&[block_hash], rng)?;
        // Derive the signer address.
        let address = Address::try_from(private_key)?;
        // Ensure the signature is valid.
        ensure!(signature.verify(&address, &[block_hash]), "Invalid signature for block {}", header.height());
        // Construct the block.
        Ok(Self { block_hash: block_hash.into(), previous_hash, header, transactions, signature })
    }

    /// Initializes a new block from a given previous hash, header, and transactions list.
    pub fn from(
        previous_hash: N::BlockHash,
        header: Header<N>,
        transactions: Transactions<N>,
        signature: Signature<N>,
    ) -> Result<Self> {
        // Ensure the block is not empty.
        ensure!(!transactions.is_empty(), "Cannot create block with no transactions");
        // Compute the block hash.
        let block_hash = N::hash_bhp1024(&[previous_hash.to_bits_le(), header.to_root()?.to_bits_le()].concat())?;
        // Derive the signer address.
        let address = signature.to_address();
        // Ensure the signature is valid.
        ensure!(signature.verify(&address, &[block_hash]), "Invalid signature for block {}", header.height());
        // Construct the block.
        Ok(Self { block_hash: block_hash.into(), previous_hash, header, transactions, signature })
    }

    /// Returns `true` if the block is well-formed.
    pub fn verify(&self, vm: &VM<N>) -> bool {
        //** Header **//

        // If the block is the genesis block, check that it is valid.
        if self.header.height() == 0 && !self.is_genesis() {
            warn!("Invalid genesis block");
            return false;
        }

        // Ensure the block header is valid.
        if !self.header.is_valid() {
            warn!("Invalid block header: {:?}", self.header);
            return false;
        }

        //** Block Hash **//

        // Compute the Merkle root of the block header.
        let header_root = match self.header.to_root() {
            Ok(root) => root,
            Err(error) => {
                warn!("Failed to compute the Merkle root of the block header: {error}");
                return false;
            }
        };

        // Check the block hash.
        match N::hash_bhp1024(&[self.previous_hash.to_bits_le(), header_root.to_bits_le()].concat()) {
            Ok(candidate_hash) => {
                // Ensure the block hash matches the one in the block.
                if candidate_hash != *self.block_hash {
                    warn!("Block {} ({}) has an incorrect block hash.", self.height(), self.block_hash);
                    return false;
                }
            }
            Err(error) => {
                warn!("Unable to compute block hash for block {} ({}): {error}", self.height(), self.block_hash);
                return false;
            }
        };

        //** Signature **//

        // TODO (howardwu): TRIAL - Update this to the validator set.
        // Ensure the block is signed by an authorized validator.
        let signer = self.signature.to_address();
        if !cfg!(test) && signer.to_string() != "aleo1q6qstg8q8shwqf5m6q5fcenuwsdqsvp4hhsgfnx5chzjm3secyzqt9mxm8" {
            warn!("Block {} ({}) is signed by an unauthorized validator: {}", self.height(), self.block_hash, signer);
            return false;
        }

        // Check the signature.
        if !self.signature.verify(&signer, &[*self.block_hash]) {
            warn!("Invalid signature for block {} ({})", self.height(), self.block_hash);
            return false;
        }

        //** Transactions **//

        // Compute the transactions root.
        match self.transactions.to_root() {
            // Ensure the transactions root matches the one in the block header.
            Ok(root) => {
                if &root != self.header.transactions_root() {
                    warn!(
                        "Block {} ({}) has an incorrect transactions root: expected {}",
                        self.height(),
                        self.block_hash,
                        self.header.transactions_root()
                    );
                    return false;
                }
            }
            Err(error) => {
                warn!("Failed to compute the Merkle root of the block transactions: {error}");
                return false;
            }
        };

        // Ensure the transactions list is not empty.
        if self.transactions.is_empty() {
            warn!("Cannot validate an empty transactions list");
            return false;
        }

        // Ensure the number of transactions is within the allowed range.
        if self.transactions.len() > Transactions::<N>::MAX_TRANSACTIONS {
            warn!("Cannot validate a block with more than {} transactions", Transactions::<N>::MAX_TRANSACTIONS);
            return false;
        }

        // Ensure each transaction is well-formed.
        if !self.transactions.par_iter().all(|(_, transaction)| vm.verify(transaction)) {
            warn!("Invalid transaction found in the transactions list");
            return false;
        }

        //** Fees **//

        // Prepare the block height, credits program ID, and genesis function name.
        let height = self.height();
        let credits_program_id = ProgramID::from_str("credits.aleo").expect("Failed to parse the credits program ID");
        let credits_genesis = Identifier::from_str("genesis").expect("Failed to parse the genesis function name");

        // Ensure the fee is correct for each transition.
        for transition in self.transitions() {
            if height > 0 {
                // Ensure the genesis function is not called.
                if *transition.program_id() == credits_program_id && *transition.function_name() == credits_genesis {
                    warn!("The genesis function cannot be called.");
                    return false;
                }
                // Ensure the transition fee is not negative.
                if transition.fee().is_negative() {
                    warn!("The transition fee cannot be negative.");
                    return false;
                }
            }
        }

        true
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
    pub const fn previous_state_root(&self) -> &Field<N> {
        self.header.previous_state_root()
    }

    /// Returns the transactions root in the block header.
    pub const fn transactions_root(&self) -> &Field<N> {
        self.header.transactions_root()
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

    /// Returns the coinbase target for this block.
    pub const fn coinbase_target(&self) -> u64 {
        self.header.coinbase_target()
    }

    /// Returns the proof target for this block.
    pub const fn proof_target(&self) -> u64 {
        self.header.proof_target()
    }

    /// Returns the Unix timestamp (UTC) for this block.
    pub const fn timestamp(&self) -> i64 {
        self.header.timestamp()
    }
}

impl<N: Network> Block<N> {
    /// Returns the transactions in this block.
    pub const fn transactions(&self) -> &Transactions<N> {
        &self.transactions
    }

    /// Returns an iterator over the transaction IDs, for all transactions in `self`.
    pub fn transaction_ids(&self) -> impl '_ + Iterator<Item = &N::TransactionID> {
        self.transactions.transaction_ids()
    }

    /// Returns an iterator over all transactions in `self` that are deployments.
    pub fn deployments(&self) -> impl '_ + Iterator<Item = &Deployment<N>> {
        self.transactions.deployments()
    }

    /// Returns an iterator over all transactions in `self` that are executions.
    pub fn executions(&self) -> impl '_ + Iterator<Item = &Execution<N>> {
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

    /// Returns an iterator over the origins, for all transition inputs that are records.
    pub fn origins(&self) -> impl '_ + Iterator<Item = &Origin<N>> {
        self.transactions.origins()
    }

    /// Returns an iterator over the tags, for all transition inputs that are records.
    pub fn tags(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.transactions.tags()
    }

    /// Returns an iterator over the serial numbers, for all transition inputs that are records.
    pub fn serial_numbers(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.transactions.serial_numbers()
    }

    /// Returns an iterator over the commitments, for all transition outputs that are records.
    pub fn commitments(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.transactions.commitments()
    }

    /// Returns an iterator over the nonces, for all transition outputs that are records.
    pub fn nonces(&self) -> impl '_ + Iterator<Item = &Group<N>> {
        self.transactions.nonces()
    }

    /// Returns an iterator over the fees, for all transitions.
    pub fn fees(&self) -> impl '_ + Iterator<Item = &i64> {
        self.transactions.fees()
    }
}
