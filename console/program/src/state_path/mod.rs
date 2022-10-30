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

mod configuration;
pub use configuration::*;

mod header_leaf;
pub use header_leaf::*;

mod transaction_leaf;
pub use transaction_leaf::*;

pub mod transition_leaf;
pub use transition_leaf::*;

mod bytes;
mod parse;
mod serialize;

use snarkvm_console_network::prelude::*;
use snarkvm_console_types::{Boolean, Field};

/// The state path proves existence of the transition leaf to either a global or local state root.
///
/// The `[[ ]]` notation is used to denote public inputs.
/// ```ignore
///
///  [[ global_state_root ]]
///           |
///      block_path
///          |
///     block_hash := Hash( previous_block_hash || header_root )
///                                                     |
///                                                header_path
///                                                    |
///                                               header_leaf
///                                                   |
///                                            transactions_path
///                                                  |
///                                            transaction_id ---> (==) <--- [[ local_state_root ]]
///                                                 |               |
///                                          transaction_path   is_local?
///                                                |
///                                         transaction_leaf
///                                               |
///                                        transition_path
///                                              |
///                                       transition_leaf
///
/// ```
#[derive(Clone, PartialEq, Eq)]
pub struct StatePath<N: Network> {
    /// The global state root (Public).
    global_state_root: N::StateRoot,
    /// The local state root (Public).
    local_state_root: Field<N>,
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
    /// A boolean indicating whether this is a global or local state root.
    is_global: Boolean<N>,
}

impl<N: Network> StatePath<N> {
    /// Initializes a new instance of `StatePath`.
    #[allow(clippy::too_many_arguments)]
    pub fn from(
        global_state_root: N::StateRoot,
        local_state_root: Field<N>,
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
        is_global: bool,
    ) -> Result<Self> {
        // Ensure the transition leaf variant is 3 (Input::Record).
        ensure!(transition_leaf.variant() == 3, "Transition leaf variant must be 3 (Input::Record)");
        // Ensure the transition path is valid.
        ensure!(
            N::verify_merkle_path_bhp(&transition_path, &transaction_leaf.id(), &transition_leaf.to_bits_le()),
            "'{}' (an input or output ID) does not belong to '{}' (a function or transition)",
            transition_leaf.id(),
            transaction_leaf.id()
        );
        // Ensure the transaction leaf variant is 1 (Transaction::Execution).
        ensure!(transaction_leaf.variant() == 1, "Transaction leaf variant must be 1 (Transaction::Execution)",);
        // Ensure the transaction path is valid.
        ensure!(
            N::verify_merkle_path_bhp(&transaction_path, &transaction_id, &transaction_leaf.to_bits_le()),
            "'{}' (a function or transition) does not belong to transaction '{transaction_id}'",
            transaction_leaf.id(),
        );

        if is_global {
            // Ensure the header leaf index is 1 (Header::transactions_root).
            ensure!(header_leaf.index() == 1, "Header leaf index must be 1 (Header::transactions_root)");
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
            // Ensure the global state root is correct.
            ensure!(
                N::verify_merkle_path_bhp(&block_path, &global_state_root, &block_hash.to_bits_le()),
                "'{block_hash}' (a block hash) does not belong to '{global_state_root}' (a global state root)",
            );
        } else {
            // Ensure the local state root is correct.
            ensure!(
                *transaction_id == local_state_root,
                "'{}' (a decoded transaction ID) does not match the '{local_state_root}' (a local state root)",
                *transaction_id
            );
        }

        // Return the state path.
        Ok(Self {
            global_state_root,
            local_state_root,
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
            is_global: Boolean::new(is_global),
        })
    }

    /// Returns the global state root.
    pub const fn global_state_root(&self) -> N::StateRoot {
        self.global_state_root
    }

    /// Returns the local state root.
    pub const fn local_state_root(&self) -> Field<N> {
        self.local_state_root
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

    /// Returns a boolean indicating whether this is a global or local state root.
    pub const fn is_global(&self) -> Boolean<N> {
        self.is_global
    }
}

#[cfg(any(test, feature = "test"))]
pub mod test_helpers {
    use super::*;
    use snarkvm_console_network::prelude::TestRng;

    /// Randomly sample a state path.
    pub fn sample_state_path<N: Network>(
        is_global: bool,
        commitment: Option<Field<N>>,
        rng: &mut TestRng,
    ) -> Result<StatePath<N>> {
        // Prepare the commitment.
        let commitment = match commitment {
            Some(commitment) => commitment,
            None => Field::rand(rng),
        };

        // Construct the transition path and transaction leaf.
        let transition_leaf = TransitionLeaf::new(0, 0, 3, commitment);
        let transition_tree: TransitionTree<N> = N::merkle_tree_bhp(&[transition_leaf.to_bits_le()])?;
        let transition_id = transition_tree.root();
        let transition_path = transition_tree.prove(0, &transition_leaf.to_bits_le())?;

        // Construct the transaction path and transaction leaf.
        let transaction_leaf = TransactionLeaf::new(1, 0, *transition_id);
        let transaction_tree: TransactionTree<N> = N::merkle_tree_bhp(&[transaction_leaf.to_bits_le()])?;
        let transaction_id = *transaction_tree.root();
        let transaction_path = transaction_tree.prove(0, &transaction_leaf.to_bits_le())?;

        // Prepare the local state root.
        let local_state_root = match is_global {
            true => Field::rand(rng), // TODO (howardwu): This likely needs to change to transaction_id for the on-chain verifier to pass.
            false => transaction_id,
        };

        // Construct the transactions path.
        let transactions_tree: TransactionsTree<N> = N::merkle_tree_bhp(&[transaction_id.to_bits_le()])?;
        let transactions_root = transactions_tree.root();
        let transactions_path = transactions_tree.prove(0, &transaction_id.to_bits_le())?;

        // Construct the block header path.
        let header_leaf = HeaderLeaf::<N>::new(1, *transactions_root);
        let header_tree: HeaderTree<N> =
            N::merkle_tree_bhp(&[Field::<N>::zero().to_bits_le(), header_leaf.to_bits_le()])?;
        let header_root = header_tree.root();
        let header_path = header_tree.prove(1, &header_leaf.to_bits_le())?;

        let previous_block_hash: N::BlockHash = Field::<N>::rand(rng).into();
        let preimage = (*previous_block_hash).to_bits_le().into_iter().chain(header_root.to_bits_le().into_iter());
        let block_hash = N::hash_bhp1024(&preimage.collect::<Vec<_>>())?;

        // Construct the global state root and block path.
        let block_tree: BlockTree<N> = N::merkle_tree_bhp(&[block_hash.to_bits_le()])?;
        let global_state_root = *block_tree.root();
        let block_path = block_tree.prove(0, &block_hash.to_bits_le())?;

        StatePath::<N>::from(
            global_state_root.into(),
            local_state_root,
            block_path,
            block_hash.into(),
            previous_block_hash,
            *header_root,
            header_path,
            header_leaf,
            transactions_path,
            transaction_id.into(),
            transaction_path,
            transaction_leaf,
            transition_path,
            transition_leaf,
            is_global,
        )
    }
}
