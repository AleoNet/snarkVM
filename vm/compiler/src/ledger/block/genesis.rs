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

impl<N: Network> Block<N> {
    /// Initializes a new genesis block.
    pub fn genesis<R: Rng + CryptoRng>(vm: &mut VM<N>, private_key: &PrivateKey<N>, rng: &mut R) -> Result<Self> {
        // Initialize the genesis program.
        let genesis = Program::genesis()?;
        // Deploy the genesis program.
        let deploy = vm.deploy(&genesis, rng)?;
        // Add the genesis program.
        vm.on_deploy(&deploy)?;

        // Prepare the caller.
        let caller = Address::try_from(private_key)?;
        // Prepare the function name.
        let function_name = FromStr::from_str("start")?;
        // Prepare the function inputs.
        let inputs = [Value::from_str(&caller.to_string())?, Value::from_str("1_100_000_000_000_000_u64")?];
        // Authorize the call to start.
        let authorization = vm.authorize(private_key, genesis.id(), function_name, &inputs, rng)?;
        // Execute the genesis program.
        let (_, execution) = vm.execute(authorization, rng)?;

        // Prepare the transactions.
        let transactions = Transactions::from(&[deploy, execution])?;
        // Prepare the block header.
        let header = Header::genesis(&transactions)?;
        // Prepare the previous block hash.
        let previous_hash = N::BlockHash::default();

        // Construct the block.
        let block = Self::from(previous_hash, header, transactions)?;
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
            // Ensure there are two transactions in the genesis block.
            && self.transactions.len() == 2
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_genesis() {
        let block = crate::ledger::vm::test_helpers::sample_genesis_block();
        // println!("{}", serde_json::to_string_pretty(&block).unwrap());
        assert!(block.is_genesis());
    }
}
