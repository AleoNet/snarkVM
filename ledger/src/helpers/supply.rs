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
    // Ensure this is a mint transition.
    ensure!(transition.is_mint(), "Invalid mint transaction: expected a mint");
    // Extract the amount from the input.
    match transition.inputs().get(1) {
        Some(Input::Public(_, Some(Plaintext::Literal(Literal::U64(amount), _)))) => Ok(**amount),
        _ => bail!("Invalid mint transaction: Missing public input (amount) in 'credits.aleo/mint'"),
    }
}

/// Returns the next total supply in microcredits, given the starting total supply and newly-confirmed transactions.
// TODO (raychu86): Include mints from the leader of each round.
pub fn update_total_supply<N: Network>(
    starting_total_supply_in_microcredits: u64,
    transactions: &Transactions<N>,
) -> Result<u64> {
    // Initialize the final total supply of microcredits.
    let mut final_total_supply = starting_total_supply_in_microcredits;

    // Iterate through the transactions to calculate the next total supply of microcredits.
    for confirmed in transactions.iter() {
        // Subtract the fee from the total supply.
        final_total_supply = final_total_supply
            .checked_sub(*confirmed.fee()?)
            .ok_or_else(|| anyhow!("The proposed fee underflows the total supply of microcredits"))?;

        // If the transaction contains a mint, add the amount to the total supply.
        if confirmed.is_mint() {
            // Retrieve the execution.
            let Some(execution) = confirmed.transaction().execution() else {
                bail!("Invalid mint transaction: expected an execution");
            };
            // Loop over the mint transitions to accumulate the amount minted.
            for transition in execution.transitions().filter(|t| t.is_mint()) {
                // Add the amount minted to the total supply.
                final_total_supply = final_total_supply
                    .checked_add(mint_amount(transition)?)
                    .ok_or_else(|| anyhow!("The proposed mint overflows the total supply of microcredits"))?;
            }
        }
    }
    // Return the final total supply in microcredits.
    Ok(final_total_supply)
}
