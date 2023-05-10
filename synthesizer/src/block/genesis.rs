// Copyright (C) 2019-2023 Aleo Systems Inc.
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
    /// Specifies the number of genesis transactions.
    const NUM_GENESIS_TRANSACTIONS: usize = 4;

    /// Initializes a new genesis block.
    pub fn genesis<C: ConsensusStorage<N>, R: Rng + CryptoRng>(
        vm: &VM<N, C>,
        private_key: &PrivateKey<N>,
        rng: &mut R,
    ) -> Result<Self> {
        // Prepare the caller.
        let caller = Address::try_from(private_key)?;
        // Prepare the locator.
        let locator = ("credits.aleo", "mint");
        // Prepare the amount for each call to the mint function.
        let amount = N::STARTING_SUPPLY.saturating_div(Self::NUM_GENESIS_TRANSACTIONS as u64);
        // Prepare the function inputs.
        let inputs = [caller.to_string(), format!("{amount}_u64")];

        // Prepare the mint transactions.
        let transactions = (0u32..Self::NUM_GENESIS_TRANSACTIONS as u32)
            .map(|index| {
                // Execute the mint function.
                let transaction = Transaction::execute(vm, private_key, locator, inputs.iter(), None, None, rng)?;
                // Prepare the confirmed transaction.
                ConfirmedTransaction::accepted_execute(index, transaction, vec![])
            })
            .collect::<Result<Transactions<_>>>()?;

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
            // Ensure there is the correct number of accepted transaction in the genesis block.
            && self.transactions.num_accepted() == Self::NUM_GENESIS_TRANSACTIONS
            // Ensure there is the correct number of rejected transaction in the genesis block.
            && self.transactions.num_rejected() == 0
            // Ensure there is the correct number of finalize operations in the genesis block.
            && self.transactions.num_finalize() == 0
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
