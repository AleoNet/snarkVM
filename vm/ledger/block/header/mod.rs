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

mod leaf;
pub use leaf::*;

mod merkle;
pub use merkle::*;

mod bytes;
mod genesis;
mod serialize;
mod string;

use crate::{
    console::{
        collections::merkle_tree::MerklePath,
        network::{prelude::*, BHPMerkleTree},
        types::Field,
    },
    ledger::Transactions,
};

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Metadata {
    /// The network ID of the block.
    network: u16,
    /// The height of this block - 4 bytes.
    height: u32,
    /// The round that produced this block - 8 bytes.
    round: u64,
    /// The coinbase target for this block - 8 bytes.
    coinbase_target: u64,
    /// The proof target for this block - 8 bytes.
    proof_target: u64,
    /// The Unix timestamp (UTC) for this block - 8 bytes.
    timestamp: i64,
}

impl ToBits for Metadata {
    /// Returns the little-endian bits of the metadata.
    fn to_bits_le(&self) -> Vec<bool> {
        vec![
            self.network.to_bits_le(),         // 2 bytes
            self.height.to_bits_le(),          // 4 bytes
            self.round.to_bits_le(),           // 8 bytes
            self.coinbase_target.to_bits_le(), // 8 bytes
            self.proof_target.to_bits_le(),    // 8 bytes
            self.timestamp.to_bits_le(),       // 8 bytes
        ]
        .concat()
    }

    /// Returns the big-endian bits of the metadata.
    fn to_bits_be(&self) -> Vec<bool> {
        vec![
            self.network.to_bits_be(),         // 2 bytes
            self.height.to_bits_be(),          // 4 bytes
            self.round.to_bits_be(),           // 8 bytes
            self.coinbase_target.to_bits_be(), // 8 bytes
            self.proof_target.to_bits_be(),    // 8 bytes
            self.timestamp.to_bits_be(),       // 8 bytes
        ]
        .concat()
    }
}

/// The header for the block contains metadata that uniquely identifies the block.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Header<N: Network> {
    /// The Merkle root representing the blocks in the ledger up to the previous block.
    previous_state_root: Field<N>,
    /// The Merkle root representing the transactions in the block.
    transactions_root: Field<N>,
    /// The block header metadata.
    metadata: Metadata,
}

impl<N: Network> Header<N> {
    /// Initializes a new block header with the given inputs.
    #[allow(clippy::too_many_arguments)]
    pub fn from(
        previous_state_root: Field<N>,
        transactions_root: Field<N>,
        network: u16,
        height: u32,
        round: u64,
        coinbase_target: u64,
        proof_target: u64,
        timestamp: i64,
    ) -> Result<Self> {
        // Construct a new block header.
        let header = Self {
            previous_state_root,
            transactions_root,
            metadata: Metadata { network, height, round, coinbase_target, proof_target, timestamp },
        };
        // Ensure the header is valid.
        match header.is_valid() {
            true => Ok(header),
            false => bail!("Invalid block header: {:?}", header),
        }
    }

    /// Returns `true` if the block header is well-formed.
    pub fn is_valid(&self) -> bool {
        match self.metadata.height == 0u32 {
            true => self.is_genesis(),
            false => {
                // Ensure the previous ledger root is nonzero.
                self.previous_state_root != Field::zero()
                    // Ensure the transactions root is nonzero.
                    && self.transactions_root != Field::zero()
                    // Ensure the network ID is correct.
                    && self.metadata.network == N::ID
                    // Ensure the height is nonzero.
                    && self.metadata.height != 0u32
                    // Ensure the round is nonzero.
                    && self.metadata.round != 0u64
                    // Ensure the coinbase target is not u64::MAX.
                    && self.metadata.coinbase_target != u64::MAX
                    // Ensure the proof target is not u64::MAX.
                    && self.metadata.proof_target != u64::MAX
                    // Ensure the timestamp in the block is nonzero.
                    && self.metadata.timestamp != 0i64
            }
        }
    }

    /// Returns the previous state root from the block header.
    pub const fn previous_state_root(&self) -> &Field<N> {
        &self.previous_state_root
    }

    /// Returns the transactions root in the block header.
    pub const fn transactions_root(&self) -> &Field<N> {
        &self.transactions_root
    }

    /// Returns the network ID of the block.
    pub const fn network(&self) -> u16 {
        self.metadata.network
    }

    /// Returns the height of the block.
    pub const fn height(&self) -> u32 {
        self.metadata.height
    }

    /// Returns the round number of the block.
    pub const fn round(&self) -> u64 {
        self.metadata.round
    }

    /// Returns the coinbase target for this block.
    pub const fn coinbase_target(&self) -> u64 {
        self.metadata.coinbase_target
    }

    /// Returns the proof target for this block.
    pub const fn proof_target(&self) -> u64 {
        self.metadata.proof_target
    }

    /// Returns the Unix timestamp (UTC) for this block.
    pub const fn timestamp(&self) -> i64 {
        self.metadata.timestamp
    }
}
