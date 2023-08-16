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

use console::{
    network::Network,
    program::{Literal, Plaintext},
    types::Address,
};
use ledger_block::{Input, Transactions, Transition};

use anyhow::{anyhow, bail, ensure, Result};

/// Returns the address that minted microcredits, given a mint transition.
pub fn mint_address<N: Network>(transition: &Transition<N>) -> Result<&Address<N>> {
    // Ensure this is a mint transition.
    ensure!(transition.is_mint(), "Invalid mint transaction: expected a mint");
    // Extract the address from the input.
    match transition.inputs().get(0) {
        Some(Input::Public(_, Some(Plaintext::Literal(Literal::Address(address), _)))) => Ok(address),
        _ => bail!("Invalid mint transaction: Missing public input (address) in 'credits.aleo/mint'"),
    }
}

/// Returns the amount minted in microcredits, given a mint transition.
pub fn mint_amount<N: Network>(transition: &Transition<N>) -> Result<u64> {
    debug_assert!(transition.is_mint(), "Invalid mint transition: expected a mint");
    // Extract the amount from the input.
    match transition.inputs().get(1) {
        Some(Input::Public(_, Some(Plaintext::Literal(Literal::U64(amount), _)))) => Ok(**amount),
        _ => bail!("Invalid mint transition: Missing public input (amount) in 'credits.aleo/mint'"),
    }
}

/// Returns the next total supply in microcredits, given the starting total supply and newly-confirmed transactions.
pub fn update_total_supply<N: Network>(
    starting_total_supply_in_microcredits: u64,
    block_reward: u64,
    puzzle_reward: u64,
    transactions: &Transactions<N>,
) -> Result<u64> {
    // Initialize the next total supply of microcredits.
    let mut next_total_supply = starting_total_supply_in_microcredits;
    // Add the block reward to the total supply.
    next_total_supply = next_total_supply.saturating_add(block_reward);
    // Add the puzzle reward to the total supply.
    next_total_supply = next_total_supply.saturating_add(puzzle_reward);

    // Iterate through the transactions to calculate the next total supply of microcredits.
    for confirmed in transactions.iter() {
        // Subtract the fee from the total supply.
        next_total_supply = next_total_supply
            .checked_sub(*confirmed.fee_amount()?)
            .ok_or_else(|| anyhow!("The proposed fee underflows the total supply of microcredits"))?;

        // Iterate over the transitions in the transaction.
        for transition in confirmed.transaction().transitions() {
            // If the transition contains a mint, add the amount to the total supply.
            if transition.is_mint() {
                // Add the amount minted to the total supply.
                next_total_supply = next_total_supply
                    .checked_add(mint_amount(transition)?)
                    .ok_or_else(|| anyhow!("The proposed mint overflows the total supply of microcredits"))?;
            }
            // If the transition contains a split, subtract the amount from the total supply.
            if transition.is_split() {
                // TODO (howardwu): Add a test that calls `split`, checks the output records - input records == 10_000u64.
                // Subtract the amount split from the total supply.
                next_total_supply = next_total_supply
                    .checked_sub(10_000u64)
                    .ok_or_else(|| anyhow!("The proposed split underflows the total supply of microcredits"))?;
            }
        }
    }
    // Return the final total supply in microcredits.
    Ok(next_total_supply)
}
