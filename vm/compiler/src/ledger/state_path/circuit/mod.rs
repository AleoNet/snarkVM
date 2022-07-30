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

pub mod header_leaf;
pub use header_leaf::*;

pub mod transaction_leaf;
pub use transaction_leaf::*;

pub mod transition_leaf;
pub use transition_leaf::*;

mod verify;

use circuit::{
    collections::merkle_tree::MerklePath,
    network::Aleo,
    types::{environment::prelude::*, Boolean, Field},
};

/// The depth of the Merkle tree for the blocks.
const BLOCKS_DEPTH: u8 = 32;
/// The depth of the Merkle tree for the block header.
const HEADER_DEPTH: u8 = 3;
/// The depth of the Merkle tree for transactions in a block.
const TRANSACTIONS_DEPTH: u8 = 16;
/// The depth of the Merkle tree for the transaction.
const TRANSACTION_DEPTH: u8 = 4;
/// The depth of the Merkle tree for the transition.
const TRANSITION_DEPTH: u8 = 4;

type BlockPath<A> = MerklePath<A, BLOCKS_DEPTH>;
type HeaderPath<A> = MerklePath<A, HEADER_DEPTH>;
type TransactionsPath<A> = MerklePath<A, TRANSACTIONS_DEPTH>;
type TransactionPath<A> = MerklePath<A, TRANSACTION_DEPTH>;
type TransitionPath<A> = MerklePath<A, TRANSITION_DEPTH>;

pub struct StatePath<A: Aleo> {
    /// The state root.
    state_root: Field<A>,
    /// The Merkle path for the block hash.
    block_path: BlockPath<A>,
    /// The block hash.
    block_hash: Field<A>,
    /// The previous block hash.
    previous_block_hash: Field<A>,
    /// The block header root.
    header_root: Field<A>,
    /// The Merkle path for the block header leaf.
    header_path: HeaderPath<A>,
    /// The block header leaf.
    header_leaf: HeaderLeaf<A>,
    /// The Merkle path for the transaction ID.
    transactions_path: TransactionsPath<A>,
    /// The transaction ID.
    transaction_id: Field<A>,
    /// The Merkle path for the transaction leaf.
    transaction_path: TransactionPath<A>,
    /// The transaction leaf.
    transaction_leaf: TransactionLeaf<A>,
    /// The Merkle path for the transition leaf.
    transition_path: TransitionPath<A>,
    /// The transition leaf.
    transition_leaf: TransitionLeaf<A>,
}

impl<A: Aleo> Inject for StatePath<A> {
    type Primitive = crate::ledger::state_path::StatePath<A::Network>;

    /// Initializes a new ciphertext circuit from a primitive.
    fn new(mode: Mode, state_path: Self::Primitive) -> Self {
        Self {
            state_root: Field::new(mode, *state_path.state_root()),
            block_path: BlockPath::new(mode, state_path.block_path().clone()),
            block_hash: Field::new(mode, *state_path.block_hash()),
            previous_block_hash: Field::new(mode, *state_path.previous_block_hash()),
            header_root: Field::new(mode, *state_path.header_root()),
            header_path: HeaderPath::new(mode, state_path.header_path().clone()),
            header_leaf: HeaderLeaf::new(mode, state_path.header_leaf().clone()),
            transactions_path: TransactionsPath::new(mode, state_path.transactions_path().clone()),
            transaction_id: Field::new(mode, **state_path.transaction_id()),
            transaction_path: TransactionPath::new(mode, state_path.transaction_path().clone()),
            transaction_leaf: TransactionLeaf::new(mode, state_path.transaction_leaf().clone()),
            transition_path: TransitionPath::new(mode, state_path.transition_path().clone()),
            transition_leaf: TransitionLeaf::new(mode, state_path.transition_leaf().clone()),
        }
    }
}

impl<A: Aleo> Eject for StatePath<A> {
    type Primitive = crate::ledger::state_path::StatePath<A::Network>;

    /// Ejects the mode of the ciphertext.
    fn eject_mode(&self) -> Mode {
        (
            &self.state_root,
            &self.block_path,
            &self.block_hash,
            &self.previous_block_hash,
            &self.header_root,
            &self.header_path,
            &self.header_leaf,
            &self.transactions_path,
            &self.transaction_id,
            &self.transaction_path,
            &self.transaction_leaf,
            &self.transition_path,
            &self.transition_leaf,
        )
            .eject_mode()
    }

    /// Ejects the ciphertext.
    fn eject_value(&self) -> Self::Primitive {
        match Self::Primitive::new(
            self.state_root.eject_value().into(),
            self.block_path.eject_value(),
            self.block_hash.eject_value().into(),
            self.previous_block_hash.eject_value().into(),
            self.header_root.eject_value(),
            self.header_path.eject_value(),
            self.header_leaf.eject_value(),
            self.transactions_path.eject_value(),
            self.transaction_id.eject_value().into(),
            self.transaction_path.eject_value(),
            self.transaction_leaf.eject_value(),
            self.transition_path.eject_value(),
            self.transition_leaf.eject_value(),
        ) {
            Ok(state_path) => state_path,
            Err(error) => A::halt(format!("Failed to eject state path: {error}")),
        }
    }
}
