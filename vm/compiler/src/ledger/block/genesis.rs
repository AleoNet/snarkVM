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
use crate::{
    coinbase_puzzle::*,
    ledger::{COINBASE_PUZZLE_DEGREE, STARTING_SUPPLY},
    ProgramStorage,
};

impl<N: Network> Block<N> {
    /// Initializes a new genesis block.
    pub fn genesis<P: ProgramStorage<N>, R: Rng + CryptoRng>(
        vm: &VM<N, P>,
        private_key: &PrivateKey<N>,
        rng: &mut R,
    ) -> Result<Self> {
        // Prepare the caller.
        let caller = Address::try_from(private_key)?;
        // Prepare the program ID.
        let program_id = FromStr::from_str("credits.aleo")?;
        // Prepare the function name.
        let function_name = FromStr::from_str("genesis")?;
        // Prepare the function inputs.
        let inputs = [Value::from_str(&caller.to_string())?, Value::from_str(&format!("{STARTING_SUPPLY}_u64"))?];
        // Authorize the call to start.
        let authorization = vm.authorize(private_key, &program_id, function_name, &inputs, rng)?;
        // Execute the genesis function.
        let transaction = Transaction::execute_authorization(vm, authorization, rng)?;

        // Prepare the transactions.
        let transactions = Transactions::from(&[transaction]);
        // Prepare the block header.
        let header = Header::genesis(&transactions)?;
        // Prepare the previous block hash.
        let previous_hash = N::BlockHash::default();

        // Generate a coinbase proof.
        let coinbase_proof = {
            let (pk, vk) = CoinbasePuzzle::<N>::load()?;

            let epoch_info = EpochInfo { epoch_number: 0, previous_block_hash: Default::default() };
            let epoch_challenge = CoinbasePuzzle::<N>::init_for_epoch(&epoch_info, COINBASE_PUZZLE_DEGREE)?;
            let nonce = u64::rand(rng);

            let prover_solution = CoinbasePuzzle::prove(&pk, &epoch_info, &epoch_challenge, &caller, nonce)?;

            // Ensure the prover solution is valid.
            if !prover_solution.verify(&vk, &epoch_info, &epoch_challenge)? {
                bail!("Failed to initialize the genesis coinbase puzzle");
            }

            let coinbase_proof =
                CoinbasePuzzle::<N>::accumulate(&pk, &epoch_info, &epoch_challenge, &[prover_solution])?;

            // Ensure the coinbase proof is valid.
            if !coinbase_proof.verify(&vk, &epoch_info, &epoch_challenge)? {
                bail!("Genesis coinbase puzzle is invalid")
            }

            coinbase_proof
        };

        // Construct the block.
        let block = Self::new(private_key, previous_hash, header, transactions, coinbase_proof, rng)?;
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
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_genesis() {
        let block = crate::ledger::test_helpers::sample_genesis_block();
        // println!("{}", serde_json::to_string_pretty(&block).unwrap());
        assert!(block.is_genesis());
    }
}
