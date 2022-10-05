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

impl<N: Network, B: BlockStorage<N>, P: ProgramStorage<N>> Ledger<N, B, P> {
    /// Returns the latest state root.
    pub const fn latest_state_root(&self) -> &Field<N> {
        self.block_tree.root()
    }

    /// Returns the latest block.
    pub fn latest_block(&self) -> Result<Block<N>> {
        self.get_block(self.current_height)
    }

    /// Returns the latest block hash.
    pub const fn latest_hash(&self) -> N::BlockHash {
        self.current_hash
    }

    /// Returns the latest block height.
    pub const fn latest_height(&self) -> u32 {
        self.current_height
    }

    /// Returns the latest round number.
    pub const fn latest_round(&self) -> u64 {
        self.current_round
    }

    /// Returns the latest block coinbase target.
    pub fn latest_coinbase_target(&self) -> Result<u64> {
        Ok(self.get_header(self.current_height)?.coinbase_target())
    }

    /// Returns the latest block proof target.
    pub fn latest_proof_target(&self) -> Result<u64> {
        Ok(self.get_header(self.current_height)?.proof_target())
    }

    /// Returns the latest block timestamp.
    pub fn latest_timestamp(&self) -> Result<i64> {
        Ok(self.get_header(self.current_height)?.timestamp())
    }

    /// Returns the latest block transactions.
    pub fn latest_transactions(&self) -> Result<Transactions<N>> {
        self.get_transactions(self.current_height)
    }

    /// Returns the latest epoch number.
    pub fn latest_epoch_number(&self) -> u64 {
        self.current_round / NUM_ROUNDS_PER_EPOCH as u64
    }

    /// Returns the latest epoch challenge.
    pub fn latest_epoch_challenge(&self) -> Result<EpochChallenge<N>> {
        // Get the latest epoch number.
        let latest_epoch_number = self.latest_epoch_number();

        // Get the epoch's starting round (multiple of `NUM_ROUNDS_PER_EPOCH`).
        let epoch_starting_round = self.current_round - self.current_round % NUM_ROUNDS_PER_EPOCH as u64;

        // Fetch the epoch block hash (last block of the previous epoch).
        let epoch_block_hash = match epoch_starting_round {
            // Return the default block hash for the genesis epoch.
            0 => Default::default(),
            // Return the block hash of the block right before the epoch updated.
            // TODO (raychu86): This needs to be fixed when rounds become decoupled from block heights.
            //  This should fetch the block hash of the latest valid block before the end of the epoch.
            round => {
                let previous_round_number = u32::try_from(round - 1)?;

                let block_hash = self.get_hash(previous_round_number)?;

                // TODO (raychu86): Remove this check if the above TODO is fixed.
                // Ensure that the height and round number do not deviate.
                if self.get_header(previous_round_number)?.round() != previous_round_number as u64 {
                    bail!("Round number does not match the block height")
                }

                block_hash
            }
        };

        EpochChallenge::new(latest_epoch_number, epoch_block_hash, COINBASE_PUZZLE_DEGREE)
    }
}
