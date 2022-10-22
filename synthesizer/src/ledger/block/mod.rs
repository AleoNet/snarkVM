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
    coinbase_puzzle::CoinbaseSolution,
    ledger::{vm::VM, Origin, Transaction, Transition, NUM_BLOCKS_PER_EPOCH},
    process::{Deployment, Execution},
};
use console::{
    account::{Address, PrivateKey, Signature},
    network::prelude::*,
    program::Value,
    types::{Field, Group},
};

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
    /// The coinbase proof.
    coinbase_proof: Option<CoinbaseSolution<N>>,
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
        coinbase_proof: Option<CoinbaseSolution<N>>,
        rng: &mut R,
    ) -> Result<Self> {
        // Ensure the block is not empty.
        ensure!(!transactions.is_empty(), "Cannot create a block with zero transactions.");
        // Compute the block hash.
        let block_hash = N::hash_bhp1024(&[previous_hash.to_bits_le(), header.to_root()?.to_bits_le()].concat())?;
        // Sign the block hash.
        let signature = private_key.sign(&[block_hash], rng)?;
        // Construct the block.
        Self::from(previous_hash, header, transactions, coinbase_proof, signature)
    }

    /// Initializes a new block from a given previous hash, header, and transactions list.
    pub fn from(
        previous_hash: N::BlockHash,
        header: Header<N>,
        transactions: Transactions<N>,
        coinbase_proof: Option<CoinbaseSolution<N>>,
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

        // Ensure that coinbase accumulator matches the coinbase proof.
        let expected_accumulator_point = match &coinbase_proof {
            Some(coinbase_proof) => coinbase_proof.to_accumulator_point()?,
            None => Field::<N>::zero(),
        };
        ensure!(
            header.coinbase_accumulator_point() == expected_accumulator_point,
            "The coinbase accumulator point in the block header does not correspond to the given coinbase proof"
        );

        // Construct the block.
        Ok(Self { block_hash: block_hash.into(), previous_hash, header, transactions, coinbase_proof, signature })
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

    /// Returns the coinbase proof.
    pub const fn coinbase_proof(&self) -> Option<&CoinbaseSolution<N>> {
        self.coinbase_proof.as_ref()
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
        self.height() / NUM_BLOCKS_PER_EPOCH
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
