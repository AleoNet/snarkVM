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

use crate::{console::network::prelude::*, TransactionLeaf, TransactionPath};
use snarkvm_compiler::{TransitionLeaf, TransitionPath};

pub struct StatePath<N: Network> {
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
    pub fn new(
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
            "'{}' (a function or transition) does not belong to transaction '{}'",
            transaction_leaf.id(),
            transaction_id
        );
        // Return the state path.
        Ok(Self { transaction_id, transaction_path, transaction_leaf, transition_path, transition_leaf })
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
        let transaction_id = FromBytes::read_le(&mut reader)?;
        let transaction_path = FromBytes::read_le(&mut reader)?;
        let transaction_leaf = FromBytes::read_le(&mut reader)?;
        let transition_path = FromBytes::read_le(&mut reader)?;
        let transition_leaf = FromBytes::read_le(&mut reader)?;

        Self::new(transaction_id, transaction_path, transaction_leaf, transition_path, transition_leaf)
            .map_err(|e| error(e.to_string()))
    }
}

impl<N: Network> ToBytes for StatePath<N> {
    /// Writes the path to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.transaction_id.write_le(&mut writer)?;
        self.transaction_path.write_le(&mut writer)?;
        self.transaction_leaf.write_le(&mut writer)?;
        self.transition_path.write_le(&mut writer)?;
        self.transition_leaf.write_le(&mut writer)
    }
}
//
// impl<N: Network> Default for StatePath<N> {
//     fn default() -> Self {
//         Self {
//             transaction_id: Default::default(),
//             transaction_path: MerklePath::default(),
//             transaction_leaf: Default::default(),
//             transition_path: MerklePath::default(),
//             transition_leaf: Default::default(),
//         }
//     }
// }
