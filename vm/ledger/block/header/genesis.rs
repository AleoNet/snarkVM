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

impl<N: Network> Header<N> {
    /// Initializes the genesis block header.
    pub fn genesis(transactions: &Transactions<N>) -> Result<Self> {
        // Prepare a genesis block header.
        let previous_state_root = Field::zero();
        let transactions_root = transactions.to_root()?;
        let network = N::ID;
        let height = 0;
        let round = 0;
        let coinbase_target = u64::MAX;
        let proof_target = u64::MAX;
        let timestamp = 0;

        // Return the genesis block header.
        Self::from(
            previous_state_root,
            transactions_root,
            network,
            height,
            round,
            coinbase_target,
            proof_target,
            timestamp,
        )
    }

    /// Returns `true` if the block header is a genesis block header.
    pub fn is_genesis(&self) -> bool {
        // Ensure the previous ledger root is zero.
        self.previous_state_root == Field::zero()
            // Ensure the transactions root is nonzero.
            && self.transactions_root != Field::zero()
            // Ensure the network ID is correct.
            && self.metadata.network == N::ID
            // Ensure the height in the genesis block is 0.
            && self.metadata.height == 0u32
            // Ensure the round in the genesis block is 0.
            && self.metadata.round == 0u64
            // Ensure the coinbase target in the genesis block is u64::MAX.
            && self.metadata.coinbase_target == u64::MAX
            // Ensure the proof target in the genesis block is u64::MAX.
            && self.metadata.proof_target == u64::MAX
            // Ensure the timestamp in the genesis block is 0.
            && self.metadata.timestamp == 0i64
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    /// Returns the expected block header size by summing its subcomponent sizes.
    /// Update this method if the contents of a block header have changed.
    fn get_expected_size<N: Network>() -> usize {
        // Previous state root and transactions root size.
        (Field::<N>::size_in_bytes() * 2)
            // Metadata size.
            + 2 + 4 + 8 + 8 + 8 + 8
            // Add an additional 2 bytes for versioning.
            + 2
    }

    #[test]
    fn test_genesis_header_size() {
        // Prepare the expected size.
        let expected_size = get_expected_size::<CurrentNetwork>();
        // Prepare the genesis block header.
        let genesis_header = *crate::ledger::vm::test_helpers::sample_genesis_block().header();
        // Ensure the size of the genesis block header is correct.
        assert_eq!(expected_size, genesis_header.to_bytes_le().unwrap().len());
    }

    #[test]
    fn test_genesis_header() {
        // Prepare the genesis block header.
        let header = *crate::ledger::vm::test_helpers::sample_genesis_block().header();
        // Ensure the block header is a genesis block header.
        assert!(header.is_genesis());

        // Ensure the genesis block contains the following.
        assert_eq!(*header.previous_state_root(), Field::zero());
        assert_eq!(header.network(), CurrentNetwork::ID);
        assert_eq!(header.height(), 0);
        assert_eq!(header.round(), 0);
        assert_eq!(header.coinbase_target(), u64::MAX);
        assert_eq!(header.proof_target(), u64::MAX);
        assert_eq!(header.timestamp(), 0);

        // Ensure the genesis block does *not* contain the following.
        assert_ne!(*header.transactions_root(), Field::zero());
    }
}
