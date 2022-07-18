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
    console::{network::prelude::*, types::Field},
    BlockPath,
    HeaderLeaf,
    HeaderPath,
    TransactionLeaf,
    TransactionPath,
    TransactionsPath,
};
use snarkvm_compiler::{TransitionLeaf, TransitionPath};

pub struct StatePath<N: Network> {
    /// The state root.
    state_root: N::StateRoot,
    /// The Merkle path for the block hash.
    block_path: BlockPath<N>,
    /// The block hash.
    block_hash: N::BlockHash,
    /// The previous block hash.
    previous_block_hash: N::BlockHash,
    /// The block header root.
    header_root: Field<N>,
    /// The Merkle path for the block header leaf.
    header_path: HeaderPath<N>,
    /// The block header leaf.
    header_leaf: HeaderLeaf<N>,
    /// The Merkle path for the transaction ID.
    transactions_path: TransactionsPath<N>,
    /// The transaction ID.
    transaction_id: N::TransactionID,
    /// The Merkle path for the transaction leaf.
    transaction_path: TransactionPath<N>,
    /// The transaction leaf.
    transaction_leaf: TransactionLeaf<N>,
    /// The Merkle path for the transition leaf.
    transition_path: TransitionPath<N>,
    /// The transition leaf.
    transition_leaf: TransitionLeaf<N>,
}

impl<N: Network> StatePath<N> {
    /// Initializes a new instance of `StatePath`.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        state_root: N::StateRoot,
        block_path: BlockPath<N>,
        block_hash: N::BlockHash,
        previous_block_hash: N::BlockHash,
        header_root: Field<N>,
        header_path: HeaderPath<N>,
        header_leaf: HeaderLeaf<N>,
        transactions_path: TransactionsPath<N>,
        transaction_id: N::TransactionID,
        transaction_path: TransactionPath<N>,
        transaction_leaf: TransactionLeaf<N>,
        transition_path: TransitionPath<N>,
        transition_leaf: TransitionLeaf<N>,
    ) -> Result<Self> {
        // Ensure the transition path is valid.
        ensure!(
            N::verify_merkle_path_bhp(&transition_path, &transaction_leaf.id(), &transition_leaf.to_bits_le()),
            "'{}' (an input or output ID) does not belong to '{}' (a function or transition)",
            transition_leaf.id(),
            transaction_leaf.id()
        );
        // Ensure the transaction path is valid.
        ensure!(
            N::verify_merkle_path_bhp(&transaction_path, &transaction_id, &transaction_leaf.to_bits_le()),
            "'{}' (a function or transition) does not belong to transaction '{transaction_id}'",
            transaction_leaf.id(),
        );
        // Ensure the transactions path is valid.
        ensure!(
            N::verify_merkle_path_bhp(&transactions_path, &header_leaf.id(), &transaction_id.to_bits_le()),
            "Transaction '{transaction_id}' does not belong to '{header_leaf}' (a header leaf)",
        );
        // Ensure the header path is valid.
        ensure!(
            N::verify_merkle_path_bhp(&header_path, &header_root, &header_leaf.to_bits_le()),
            "'{header_leaf}' (a header leaf) does not belong to '{block_hash}' (a block header)",
        );
        // Ensure the block hash is correct.
        let preimage = (*previous_block_hash).to_bits_le().into_iter().chain(header_root.to_bits_le().into_iter());
        ensure!(
            *block_hash == N::hash_bhp1024(&preimage.collect::<Vec<_>>())?,
            "Block hash '{block_hash}' is incorrect. Double-check the previous block hash and block header root."
        );
        // Ensure the state root is correct.
        ensure!(
            N::verify_merkle_path_bhp(&block_path, &state_root, &block_hash.to_bits_le()),
            "'{block_hash}' (a block hash) does not belong to '{state_root}' (a state root)",
        );
        // Return the state path.
        Ok(Self {
            state_root,
            block_path,
            block_hash,
            previous_block_hash,
            header_root,
            header_path,
            header_leaf,
            transactions_path,
            transaction_id,
            transaction_path,
            transaction_leaf,
            transition_path,
            transition_leaf,
        })
    }

    /// Returns the state root.
    pub const fn state_root(&self) -> N::StateRoot {
        self.state_root
    }

    /// Returns the block path.
    pub const fn block_path(&self) -> &BlockPath<N> {
        &self.block_path
    }

    /// Returns the block hash.
    pub const fn block_hash(&self) -> N::BlockHash {
        self.block_hash
    }

    /// Returns the previous block hash.
    pub const fn previous_block_hash(&self) -> N::BlockHash {
        self.previous_block_hash
    }

    /// Returns the block header root.
    pub const fn header_root(&self) -> &Field<N> {
        &self.header_root
    }

    /// Returns the header path.
    pub const fn header_path(&self) -> &HeaderPath<N> {
        &self.header_path
    }

    /// Returns the header leaf.
    pub const fn header_leaf(&self) -> &HeaderLeaf<N> {
        &self.header_leaf
    }

    /// Returns the transactions path.
    pub const fn transactions_path(&self) -> &TransactionsPath<N> {
        &self.transactions_path
    }

    /// Returns the transaction ID.
    pub const fn transaction_id(&self) -> &N::TransactionID {
        &self.transaction_id
    }

    /// Returns the Merkle path for the transaction leaf.
    pub const fn transaction_path(&self) -> &TransactionPath<N> {
        &self.transaction_path
    }

    /// Returns the transaction leaf.
    pub const fn transaction_leaf(&self) -> &TransactionLeaf<N> {
        &self.transaction_leaf
    }

    /// Returns the Merkle path for the transition leaf.
    pub const fn transition_path(&self) -> &TransitionPath<N> {
        &self.transition_path
    }

    /// Returns the transition leaf.
    pub const fn transition_leaf(&self) -> &TransitionLeaf<N> {
        &self.transition_leaf
    }
}

impl<N: Network> FromBytes for StatePath<N> {
    /// Reads the path from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let state_root = N::StateRoot::read_le(&mut reader)?;
        let block_path = BlockPath::read_le(&mut reader)?;
        let block_hash = N::BlockHash::read_le(&mut reader)?;
        let previous_block_hash = N::BlockHash::read_le(&mut reader)?;
        let header_root = Field::read_le(&mut reader)?;
        let header_path = HeaderPath::read_le(&mut reader)?;
        let header_leaf = HeaderLeaf::read_le(&mut reader)?;
        let transactions_path = TransactionsPath::read_le(&mut reader)?;
        let transaction_id = FromBytes::read_le(&mut reader)?;
        let transaction_path = FromBytes::read_le(&mut reader)?;
        let transaction_leaf = FromBytes::read_le(&mut reader)?;
        let transition_path = FromBytes::read_le(&mut reader)?;
        let transition_leaf = FromBytes::read_le(&mut reader)?;

        Self::new(
            state_root,
            block_path,
            block_hash,
            previous_block_hash,
            header_root,
            header_path,
            header_leaf,
            transactions_path,
            transaction_id,
            transaction_path,
            transaction_leaf,
            transition_path,
            transition_leaf,
        )
        .map_err(|e| error(e.to_string()))
    }
}

impl<N: Network> ToBytes for StatePath<N> {
    /// Writes the path to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.state_root.write_le(&mut writer)?;
        self.block_path.write_le(&mut writer)?;
        self.block_hash.write_le(&mut writer)?;
        self.previous_block_hash.write_le(&mut writer)?;
        self.header_root.write_le(&mut writer)?;
        self.header_path.write_le(&mut writer)?;
        self.header_leaf.write_le(&mut writer)?;
        self.transactions_path.write_le(&mut writer)?;
        self.transaction_id.write_le(&mut writer)?;
        self.transaction_path.write_le(&mut writer)?;
        self.transaction_leaf.write_le(&mut writer)?;
        self.transition_path.write_le(&mut writer)?;
        self.transition_leaf.write_le(&mut writer)
    }
}
