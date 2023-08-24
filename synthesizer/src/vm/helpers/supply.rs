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

use anyhow::{bail, ensure, Result};
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
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
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
    /// Updates the supply after an initial public balance has been added.
    pub fn add_initial_public_balance(&mut self, amount: u64) -> Result<()> {
        self.total = self.total.saturating_add(amount);
        self.public = self.public.saturating_add(amount);

        Ok(())
    }

    /// Updates the supply after an initial committee member has been added.
    pub fn add_initial_committee_member(&mut self, amount: u64) -> Result<()> {
        self.total = self.total.saturating_add(amount);
        self.staked = self.staked.saturating_add(amount);

        Ok(())
    }

    /// Updates the supply with a `bond_public` operation.
    pub fn bond_public(&mut self, amount: u64) -> Result<()> {
        ensure!(self.public > amount, "Failed to perform `bond_public` - insufficient public supply");

        self.public = self.public.saturating_sub(amount);
        self.staked = self.staked.saturating_add(amount);

        Ok(())
    }

    /// Updates the supply with an `unbond_public` operation.
    pub fn unbond_public(&mut self, amount: u64) -> Result<()> {
        ensure!(self.staked > amount, "Failed to perform `unbond_public` - insufficient staked supply");

        self.staked = self.staked.saturating_sub(amount);
        self.public = self.public.saturating_add(amount);

        Ok(())
    }

    /// Updates the supply with a `block_reward` operation.
    pub fn block_reward(&mut self, amount: u64) -> Result<()> {
        self.total = self.total.saturating_add(amount);
        self.public = self.public.saturating_add(amount);

        Ok(())
    }

    /// Updates the supply with a `coinbase_reward` operation.
    pub fn puzzle_reward(&mut self, amount: u64) -> Result<()> {
        self.total = self.total.saturating_add(amount);
        self.staked = self.staked.saturating_add(amount);

        Ok(())
    }

    /// Updates the supply with a `fee_public` operation.
    pub fn fee_public(&mut self, amount: u64) -> Result<()> {
        ensure!(self.total > amount, "Failed to perform `fee_public` - insufficient total supply");
        ensure!(self.public > amount, "Failed to perform `fee_public` - insufficient public supply");

        self.total = self.total.saturating_sub(amount);
        self.public = self.public.saturating_sub(amount);

        Ok(())
    }

    /// Updates the supply with a `fee_private` operation.
    pub fn fee_private(&mut self, amount: u64) -> Result<()> {
        ensure!(self.total > amount, "Failed to perform `fee_private` - insufficient total supply");
        ensure!(self.private > amount, "Failed to perform `fee_private` - insufficient private supply");

        self.total = self.total.saturating_sub(amount);
        self.private = self.private.saturating_sub(amount);

        Ok(())
    }

    /// Updates the supply with a `split` operation.
    pub fn split(&mut self) -> Result<()> {
        const SPLIT_FEE: u64 = 10_000;

        ensure!(self.total > SPLIT_FEE, "Failed to perform `split` - insufficient total supply");
        ensure!(self.private > SPLIT_FEE, "Failed to perform `split` - insufficient private supply");

        self.total = self.total.saturating_sub(SPLIT_FEE);
        self.private = self.private.saturating_sub(SPLIT_FEE);

        Ok(())
    }

    /// Updates the supply with a `transfer_public_to_private` operation.
    pub fn transfer_public_to_private(&mut self, amount: u64) -> Result<()> {
        ensure!(self.public > amount, "Failed to perform `transfer_public_to_private` - insufficient public supply");

        self.public = self.public.saturating_sub(amount);
        self.private = self.private.saturating_add(amount);

        Ok(())
    }

    /// Updates the supply with a `transfer_private_to_public` operation.
    pub fn transfer_private_to_public(&mut self, amount: u64) -> Result<()> {
        ensure!(self.private > amount, "Failed to perform `transfer_private_to_public` - insufficient private supply");

        self.private = self.private.saturating_sub(amount);
        self.public = self.public.saturating_add(amount);

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

    Ok(Supply { total, private, public, staked })
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
