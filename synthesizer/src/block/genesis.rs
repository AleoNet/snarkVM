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
use crate::ConsensusStorage;

impl<N: Network> Block<N> {
    /// Initializes a new genesis block.
    pub fn genesis<C: ConsensusStorage<N>, R: Rng + CryptoRng>(
        vm: &VM<N, C>,
        private_key: &PrivateKey<N>,
        rng: &mut R,
    ) -> Result<Self> {
        // Prepare the caller.
        let caller = Address::try_from(private_key)?;
        // Prepare the function inputs.
        let inputs = [caller.to_string(), format!("{}_u64", N::STARTING_SUPPLY)];
        // Authorize the call to start.
        let authorization = vm.authorize(private_key, "credits.aleo", "mint", inputs, rng)?;
        // Execute the genesis function.
        let transaction = Transaction::execute_authorization(vm, authorization, None, rng)?;

        // Prepare the transactions.
        let transactions = Transactions::from(&[transaction]);
        // Prepare the block header.
        let header = Header::genesis(&transactions)?;
        // Prepare the previous block hash.
        let previous_hash = N::BlockHash::default();

        // Prepare the coinbase solution.
        let coinbase_solution = None; // The genesis block does not require a coinbase solution.

        // Construct the block.
        let block = Self::new(private_key, previous_hash, header, transactions, coinbase_solution, rng)?;
        // Ensure the block is valid genesis block.
        match block.is_genesis() {
            true => Ok(block),
            false => bail!("Failed to initialize a genesis block"),
        }
    }

    /// Returns `true` if the block is a genesis block.
    pub fn is_genesis(&self) -> bool {
        // Ensure the previous block hash is zero.
        self.previous_hash == N::BlockHash::default()
            // Ensure the header is a genesis block header.
            && self.header.is_genesis()
            // Ensure there is 1 transaction in the genesis block.
            && self.transactions.len() == 1
            // Ensure the coinbase solution does not exist.
            && self.coinbase.is_none()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_genesis() {
        let mut rng = TestRng::default();

        // Load the genesis block.
        let genesis_block = Block::<CurrentNetwork>::read_le(CurrentNetwork::genesis_bytes()).unwrap();
        assert!(genesis_block.is_genesis());

        // Sample a new genesis block.
        let new_genesis_block = crate::vm::test_helpers::sample_genesis_block(&mut rng);
        // println!("{}", serde_json::to_string_pretty(&block).unwrap());
        assert!(new_genesis_block.is_genesis());
    }
}
