// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#![allow(clippy::redundant_closure)]

use console::{
    network::Network,
    program::{Literal, Plaintext, Value},
    types::{U64, U8},
};

use anyhow::{anyhow, bail, ensure, Result};
use indexmap::IndexMap;

/// The supply type.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SupplyType {
    Total = 0,
    Private = 1,
    Public = 2,
    Staked = 3,
}

impl SupplyType {
    pub fn from_u8(value: u8) -> Result<Self> {
        match value {
            0 => Ok(Self::Total),
            1 => Ok(Self::Private),
            2 => Ok(Self::Public),
            3 => Ok(Self::Staked),
            _ => bail!("Invalid supply type"),
        }
    }
}

/// The supply tracker for microcredits in `credits.aleo`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Supply {
    total: u64,
    private: u64,
    public: u64,
    staked: u64,
}

impl Supply {
    /// Returns the total supply.
    pub fn total(&self) -> u64 {
        self.total
    }

    /// Returns the private supply.
    pub fn private(&self) -> u64 {
        self.private
    }

    /// Returns the public supply.
    pub fn public(&self) -> u64 {
        self.public
    }

    /// Returns the staked supply.
    pub fn staked(&self) -> u64 {
        self.staked
    }
}

impl Supply {
    /// Initializes a new supply tracker from the given values.
    pub fn from(total: u64, private: u64, public: u64, staked: u64) -> Result<Self> {
        // Ensure that the total supply is the sum of the private, public, and staked supplies.
        let expected_total = private
            .checked_add(public)
            .and_then(|sum| sum.checked_add(staked))
            .ok_or(anyhow!("Overflowed total amount"))?;
        ensure!(total == expected_total, "Invalid total amount");

        // Return the supply tracker.
        Ok(Self { total, private, public, staked })
    }

    /// Updates the supply after an initial public balance has been added.
    pub fn add_initial_public_balance(&mut self, amount: u64) -> Result<()> {
        self.total = self
            .total
            .checked_add(amount)
            .ok_or(anyhow!("Failed to perform `add_initial_public_balance` - overflowed total supply"))?;
        self.public = self
            .public
            .checked_add(amount)
            .ok_or(anyhow!("Failed to perform `add_initial_public_balance` - overflowed public supply"))?;

        Ok(())
    }

    /// Updates the supply after an initial committee member has been added.
    pub fn add_initial_committee_member(&mut self, amount: u64) -> Result<()> {
        self.total = self
            .total
            .checked_add(amount)
            .ok_or(anyhow!("Failed to perform `add_initial_committee_member` - overflowed total supply"))?;
        self.staked = self
            .staked
            .checked_add(amount)
            .ok_or(anyhow!("Failed to perform `add_initial_committee_member` - overflowed staked supply"))?;

        Ok(())
    }

    /// Updates the supply with a `bond_public` operation.
    pub fn bond_public(&mut self, amount: u64) -> Result<()> {
        self.public = self
            .public
            .checked_sub(amount)
            .ok_or(anyhow!("Failed to perform `bond_public` - insufficient public supply"))?;
        self.staked = self
            .staked
            .checked_add(amount)
            .ok_or(anyhow!("Failed to perform `bond_public` - overflowed staked supply"))?;

        Ok(())
    }

    /// Updates the supply with an `unbond_public` operation.
    pub fn unbond_public(&mut self, amount: u64) -> Result<()> {
        self.staked = self
            .staked
            .checked_sub(amount)
            .ok_or(anyhow!("Failed to perform `unbond_public` - insufficient staked supply"))?;
        self.public = self
            .public
            .checked_add(amount)
            .ok_or(anyhow!("Failed to perform `unbond_public` - overflowed public supply"))?;

        Ok(())
    }

    /// Updates the supply with a `block_reward` operation.
    pub fn block_reward(&mut self, amount: u64) -> Result<()> {
        self.total = self
            .total
            .checked_add(amount)
            .ok_or(anyhow!("Failed to perform `block_reward` - overflowed total supply"))?;
        self.public = self
            .public
            .checked_add(amount)
            .ok_or(anyhow!("Failed to perform `block_reward` - overflowed public supply"))?;

        Ok(())
    }

    /// Updates the supply with a `coinbase_reward` operation.
    pub fn puzzle_reward(&mut self, amount: u64) -> Result<()> {
        self.total = self
            .total
            .checked_add(amount)
            .ok_or(anyhow!("Failed to perform `puzzle_reward` - overflowed total supply"))?;
        self.staked = self
            .staked
            .checked_add(amount)
            .ok_or(anyhow!("Failed to perform `puzzle_reward` - overflowed staked supply"))?;

        Ok(())
    }

    /// Updates the supply with a `fee_public` operation.
    pub fn fee_public(&mut self, amount: u64) -> Result<()> {
        self.total = self
            .total
            .checked_sub(amount)
            .ok_or(anyhow!("Failed to perform `fee_public` - insufficient total supply"))?;
        self.public = self
            .public
            .checked_sub(amount)
            .ok_or(anyhow!("Failed to perform `fee_public` - insufficient public supply"))?;

        Ok(())
    }

    /// Updates the supply with a `fee_private` operation.
    pub fn fee_private(&mut self, amount: u64) -> Result<()> {
        self.total = self
            .total
            .checked_sub(amount)
            .ok_or(anyhow!("Failed to perform `fee_private` - insufficient total supply"))?;
        self.private = self
            .private
            .checked_sub(amount)
            .ok_or(anyhow!("Failed to perform `fee_private` - insufficient private supply"))?;

        Ok(())
    }

    /// Updates the supply with a `split` operation.
    pub fn split(&mut self) -> Result<()> {
        const SPLIT_FEE: u64 = 10_000;

        self.total = self
            .total
            .checked_sub(SPLIT_FEE)
            .ok_or(anyhow!("Failed to perform `split` - insufficient total supply"))?;
        self.private = self
            .private
            .checked_sub(SPLIT_FEE)
            .ok_or(anyhow!("Failed to perform `split` - insufficient private supply"))?;

        Ok(())
    }

    /// Updates the supply with a `transfer_public_to_private` operation.
    pub fn transfer_public_to_private(&mut self, amount: u64) -> Result<()> {
        self.public = self
            .public
            .checked_sub(amount)
            .ok_or(anyhow!("Failed to perform `transfer_public_to_private` - insufficient public supply"))?;
        self.private = self
            .private
            .checked_add(amount)
            .ok_or(anyhow!("Failed to perform `transfer_public_to_private` - overflowed private supply"))?;

        Ok(())
    }

    /// Updates the supply with a `transfer_private_to_public` operation.
    pub fn transfer_private_to_public(&mut self, amount: u64) -> Result<()> {
        self.private = self
            .private
            .checked_sub(amount)
            .ok_or(anyhow!("Failed to perform `transfer_private_to_public` - insufficient private supply"))?;
        self.public = self
            .public
            .checked_add(amount)
            .ok_or(anyhow!("Failed to perform `transfer_private_to_public` - overflowed public supply"))?;

        Ok(())
    }
}

/// Returns the supply given the supply map from finalize storage.
pub fn supply_map_into_supply<N: Network>(supply_map: Vec<(Plaintext<N>, Value<N>)>) -> Result<Supply> {
    // Convert the given key and value into a staker entry.
    let convert = |key, value| {
        // Extract the type from the key.
        let supply_type = match key {
            Plaintext::Literal(Literal::U8(s), _) => SupplyType::from_u8(*s)?,
            _ => bail!("Invalid supply key - {key}"),
        };
        // Extract the bonded state from the value.
        match &value {
            Value::Plaintext(Plaintext::Literal(Literal::U64(amount), _)) => {
                // Return the bonded state.
                Ok((supply_type, **amount))
            }
            _ => bail!("Invalid supply value - {value}"),
        }
    };

    // Convert the supply map into amounts.
    let supply_amounts =
        supply_map.into_iter().map(|(key, value)| convert(key, value)).collect::<Result<IndexMap<_, _>>>()?;

    // Fetch the supply amounts.
    let total = *supply_amounts.get(&SupplyType::Total).unwrap_or(&0);
    let private = *supply_amounts.get(&SupplyType::Private).unwrap_or(&0);
    let public = *supply_amounts.get(&SupplyType::Public).unwrap_or(&0);
    let staked = *supply_amounts.get(&SupplyType::Staked).unwrap_or(&0);

    // Return the supply.
    Supply::from(total, private, public, staked)
}

/// Returns the supply map and bonded map, given the supply.
pub fn to_next_supply_mapping<N: Network>(next_supply: &Supply) -> Vec<(Plaintext<N>, Value<N>)> {
    vec![
        // Add the total supply.
        (
            Plaintext::Literal(Literal::U8(U8::new(SupplyType::Total as u8)), Default::default()),
            Value::Plaintext(Plaintext::Literal(Literal::U64(U64::new(next_supply.total())), Default::default())),
        ),
        // Add the private supply.
        (
            Plaintext::Literal(Literal::U8(U8::new(SupplyType::Private as u8)), Default::default()),
            Value::Plaintext(Plaintext::Literal(Literal::U64(U64::new(next_supply.private())), Default::default())),
        ),
        // Add the public supply.
        (
            Plaintext::Literal(Literal::U8(U8::new(SupplyType::Public as u8)), Default::default()),
            Value::Plaintext(Plaintext::Literal(Literal::U64(U64::new(next_supply.public())), Default::default())),
        ),
        // Add the staked supply.
        (
            Plaintext::Literal(Literal::U8(U8::new(SupplyType::Staked as u8)), Default::default()),
            Value::Plaintext(Plaintext::Literal(Literal::U64(U64::new(next_supply.staked())), Default::default())),
        ),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::{network::Testnet3, prelude::TestRng};

    type CurrentNetwork = Testnet3;

    use rand::Rng;

    const ITERATIONS: u64 = 1000;

    /// Returns a random supply.
    fn sample_supply(rng: &mut TestRng) -> Supply {
        // Sample supply amounts.
        let private: u64 = rng.gen();
        let public: u64 = rng.gen_range(0..u64::MAX - private);
        let staked: u64 = rng.gen_range(0..u64::MAX - (private + public));
        let total: u64 = private.saturating_add(public).saturating_add(staked);

        Supply::from(total, private, public, staked).unwrap()
    }

    #[test]
    fn test_to_next_supply_map() {
        let rng = &mut TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a supply.
            let supply = sample_supply(rng);

            // Convert the supply into a supply map.
            let supply_map = to_next_supply_mapping::<CurrentNetwork>(&supply);
            // Convert the supply map into a supply.
            let next_supply = supply_map_into_supply(supply_map).unwrap();

            assert_eq!(next_supply, supply);
        }
    }

    #[test]
    fn test_supply_add_initial_public_balance() {
        let rng = &mut TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a supply.
            let mut supply = sample_supply(rng);

            // Sample an amount.
            let amount = rng.gen_range(0..u64::MAX - supply.total());

            let expected_total = supply.total() + amount;
            let expected_public = supply.public() + amount;

            // Perform an `add_initial_public_balance`.
            supply.add_initial_public_balance(amount).unwrap();

            // Ensure the supply was updated correctly.
            assert_eq!(supply.total(), expected_total);
            assert_eq!(supply.public(), expected_public);

            // Check that overflows will be caught.
            let overflow_amount = u64::MAX - supply.total() + 1;
            assert!(supply.add_initial_public_balance(overflow_amount).is_err());
        }
    }

    #[test]
    fn test_supply_add_initial_committee_member() {
        let rng = &mut TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a supply.
            let mut supply = sample_supply(rng);

            // Sample an amount.
            let amount = rng.gen_range(0..u64::MAX - supply.total());

            let expected_total = supply.total() + amount;
            let expected_staked = supply.staked() + amount;

            // Perform an `add_initial_committee_member`.
            supply.add_initial_committee_member(amount).unwrap();

            // Ensure the supply was updated correctly.
            assert_eq!(supply.total(), expected_total);
            assert_eq!(supply.staked(), expected_staked);

            // Check that overflows will be caught.
            let overflow_amount = u64::MAX - supply.total() + 1;
            assert!(supply.add_initial_committee_member(overflow_amount).is_err());
        }
    }

    #[test]
    fn test_supply_bond_public() {
        let rng = &mut TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a supply.
            let mut supply = sample_supply(rng);

            // Sample an amount.
            let amount = rng.gen_range(0..supply.public());

            let expected_public = supply.public() - amount;
            let expected_staked = supply.staked() + amount;

            // Perform a `bond_public`.
            supply.bond_public(amount).unwrap();

            // Ensure the supply was updated correctly.
            assert_eq!(supply.public(), expected_public);
            assert_eq!(supply.staked(), expected_staked);

            // Check that insufficient balances will be caught.
            let underflow_amount = supply.public() + 1;
            assert!(supply.bond_public(underflow_amount).is_err());
        }
    }

    #[test]
    fn test_supply_unbond_public() {
        let rng = &mut TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a supply.
            let mut supply = sample_supply(rng);

            // Sample an amount.
            let amount = rng.gen_range(0..supply.staked());

            let expected_public = supply.public() + amount;
            let expected_staked = supply.staked() - amount;

            // Perform a `unbond_public`.
            supply.unbond_public(amount).unwrap();

            // Ensure the supply was updated correctly.
            assert_eq!(supply.public(), expected_public);
            assert_eq!(supply.staked(), expected_staked);

            // Check that insufficient balances will be caught.
            let underflow_amount = supply.staked() + 1;
            assert!(supply.unbond_public(underflow_amount).is_err());
        }
    }

    #[test]
    fn test_supply_block_reward() {
        let rng = &mut TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a supply.
            let mut supply = sample_supply(rng);

            // Sample an amount.
            let amount = rng.gen_range(0..u64::MAX - supply.total());

            let expected_total = supply.total() + amount;
            let expected_public = supply.public() + amount;

            // Perform a `block_reward`.
            supply.block_reward(amount).unwrap();

            // Ensure the supply was updated correctly.
            assert_eq!(supply.total(), expected_total);
            assert_eq!(supply.public(), expected_public);

            // Check that overflows will be caught.
            let overflow_amount = u64::MAX - supply.total() + 1;
            assert!(supply.block_reward(overflow_amount).is_err());
        }
    }

    #[test]
    fn test_supply_puzzle_reward() {
        let rng = &mut TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a supply.
            let mut supply = sample_supply(rng);

            // Sample an amount.
            let amount = rng.gen_range(0..u64::MAX - supply.total());

            let expected_total = supply.total() + amount;
            let expected_staked = supply.staked() + amount;

            // Perform a `puzzle_reward`.
            supply.puzzle_reward(amount).unwrap();

            // Ensure the supply was updated correctly.
            assert_eq!(supply.total(), expected_total);
            assert_eq!(supply.staked(), expected_staked);

            // Check that overflows will be caught.
            let overflow_amount = u64::MAX - supply.total() + 1;
            assert!(supply.puzzle_reward(overflow_amount).is_err());
        }
    }

    #[test]
    fn test_supply_fee_public() {
        let rng = &mut TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a supply.
            let mut supply = sample_supply(rng);

            // Sample an amount.
            let amount = rng.gen_range(0..supply.public());

            let expected_total = supply.total() - amount;
            let expected_public = supply.public() - amount;

            // Perform a `fee_public`.
            supply.fee_public(amount).unwrap();

            // Ensure the supply was updated correctly.
            assert_eq!(supply.total(), expected_total);
            assert_eq!(supply.public(), expected_public);

            // Check that insufficient balances will be caught.
            let underflow_amount = supply.total() + 1;
            assert!(supply.fee_public(underflow_amount).is_err());

            let underflow_amount = supply.public() + 1;
            assert!(supply.fee_public(underflow_amount).is_err());
        }
    }

    #[test]
    fn test_supply_fee_private() {
        let rng = &mut TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a supply.
            let mut supply = sample_supply(rng);

            // Sample an amount.
            let amount = rng.gen_range(0..supply.private());

            let expected_total = supply.total() - amount;
            let expected_private = supply.private() - amount;

            // Perform a `fee_private`.
            supply.fee_private(amount).unwrap();

            // Ensure the supply was updated correctly.
            assert_eq!(supply.total(), expected_total);
            assert_eq!(supply.private(), expected_private);

            // Check that insufficient balances will be caught.
            let underflow_amount = supply.total() + 1;
            assert!(supply.fee_private(underflow_amount).is_err());

            let underflow_amount = supply.private() + 1;
            assert!(supply.fee_private(underflow_amount).is_err());
        }
    }

    #[test]
    fn test_supply_split() {
        let rng = &mut TestRng::default();
        const SPLIT_FEE: u64 = 10_000;

        for _ in 0..ITERATIONS {
            // Sample a supply.
            let mut supply = sample_supply(rng);

            let expected_total = supply.total() - SPLIT_FEE;
            let expected_private = supply.private() - SPLIT_FEE;

            // Perform a `split`.
            supply.split().unwrap();

            // Ensure the supply was updated correctly.
            assert_eq!(supply.total(), expected_total);
            assert_eq!(supply.private(), expected_private);
        }

        // Check that splits will fail if there is insufficient balance.
        let mut new_supply: Supply = Default::default();
        assert!(new_supply.split().is_err());
    }

    #[test]
    fn test_supply_transfer_public_to_private() {
        let rng = &mut TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a supply.
            let mut supply = sample_supply(rng);

            // Sample an amount.
            let amount = rng.gen_range(0..supply.public());

            let expected_public = supply.public() - amount;
            let expected_private = supply.private() + amount;

            // Perform a `transfer_public_to_private`.
            supply.transfer_public_to_private(amount).unwrap();

            // Ensure the supply was updated correctly.
            assert_eq!(supply.public(), expected_public);
            assert_eq!(supply.private(), expected_private);

            // Check that insufficient balances will be caught.
            let underflow_amount = supply.public() + 1;
            assert!(supply.transfer_public_to_private(underflow_amount).is_err());
        }
    }

    #[test]
    fn test_supply_transfer_private_to_public() {
        let rng = &mut TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a supply.
            let mut supply = sample_supply(rng);

            // Sample an amount.
            let amount = rng.gen_range(0..supply.private());

            let expected_public = supply.public() + amount;
            let expected_private = supply.private() - amount;

            // Perform a `transfer_private_to_public`.
            supply.transfer_private_to_public(amount).unwrap();

            // Ensure the supply was updated correctly.
            assert_eq!(supply.public(), expected_public);
            assert_eq!(supply.private(), expected_private);

            // Check that insufficient balances will be caught.
            let underflow_amount = supply.private() + 1;
            assert!(supply.transfer_private_to_public(underflow_amount).is_err());
        }
    }
}
