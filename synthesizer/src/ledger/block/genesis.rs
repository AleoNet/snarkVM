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
use crate::{ledger::STARTING_SUPPLY, ProgramStorage};

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

        // Prepare the coinbase proof.
        let coinbase_proof = None; // The genesis block does not require a coinbase proof.

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
            // Ensure the coinbase proof does not exist.
            && self.coinbase_proof.is_none()
    }
}

#[cfg(test)]
mod tests {
    use snarkvm_utilities::TestRng;

    #[test]
    fn test_genesis() {
        let mut rng = TestRng::default();

        let block = crate::ledger::test_helpers::sample_genesis_block(&mut rng);
        // println!("{}", serde_json::to_string_pretty(&block).unwrap());
        assert!(block.is_genesis());
    }
}
