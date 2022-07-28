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

use super::*;

// TODO (raychu86): Inject this check into the `execute` call.

impl<A: Aleo> StatePath<A> {
    /// Returns `true` if the state path is valid for the given `commitment`.
    pub fn verify(&self, commitment: &Field<A>) -> Boolean<A> {
        // TODO (raychu86): Construct the transition id from the commitment.

        // Ensure the transition path is valid.
        let transition_path_is_valid = A::verify_merkle_path_bhp(
            &self.transition_path,
            self.transition_leaf.id(),
            &self.transition_leaf.to_bits_le(),
        );

        // Ensure the transaction path is valid.
        let transaction_path_is_valid = A::verify_merkle_path_bhp(
            &self.transaction_path,
            self.transaction_leaf.id(),
            &self.transaction_leaf.to_bits_le(),
        );

        // Ensure the transactions path is valid.
        let transactions_path_is_valid =
            A::verify_merkle_path_bhp(&self.transactions_path, &self.transaction_id, &self.transaction_id.to_bits_le());

        // Ensure the header path is valid.
        let header_path_is_valid =
            A::verify_merkle_path_bhp(&self.header_path, &self.header_root, &self.header_leaf.id().to_bits_le());

        // Ensure the block hash is correct.
        let block_hash_preimage = self
            .previous_block_hash
            .to_bits_le()
            .into_iter()
            .chain(self.header_root.to_bits_le().into_iter())
            .collect::<Vec<_>>();

        let block_hash_is_valid = A::hash_bhp1024(&block_hash_preimage).is_equal(&self.block_hash);

        // Ensure the state root is correct.
        let state_root_is_valid =
            A::verify_merkle_path_bhp(&self.block_path, &self.state_root, &self.block_hash.to_bits_le());

        transition_path_is_valid
            .is_equal(&transaction_path_is_valid)
            .is_equal(&transactions_path_is_valid)
            .is_equal(&header_path_is_valid)
            .is_equal(&block_hash_is_valid)
            .is_equal(&state_root_is_valid)
    }
}
