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

use console::network::prelude::*;
use ledger_block::Ratify;
use ledger_coinbase::PartialSolution;

use anyhow::Result;

/// Returns the proving rewards for a given coinbase reward, list of partial prover solutions, accumulated proof target, and coinbase target.
///
/// The prover reward is defined as:
///   1/2 * coinbase_reward * (prover_target / combined_proof_target) * ((coinbase_target - accumulated_proof_target) / coinbase_target)
///   = 1/2 * coinbase_reward * (prover_target / combined_proof_target) * (remaining_coinbase_target / coinbase_target)
///   = (coinbase_reward * prover_target * remaining_coinbase_target) / (2 * combined_proof_target * coinbase_target)
pub fn proving_rewards<N: Network>(
    partial_solutions: &[PartialSolution<N>],
    coinbase_reward: u64,
    combined_proof_target: u128,
    accumulated_proof_target: u64,
    coinbase_target: u64,
) -> Result<Vec<Ratify<N>>> {
    // Initialize a vector to store the proving rewards.
    let mut proving_rewards = Vec::with_capacity(partial_solutions.len());

    // Compute the remaining coinbase target.
    let remaining_coinbase_target = coinbase_target
        .checked_sub(accumulated_proof_target)
        .ok_or_else(|| anyhow!("Coinbase target is less than the accumulated proof target"))?;

    // Ensure the remaining coinbase target is greater than 0.
    ensure!(remaining_coinbase_target > 0, "Remaining coinbase target must be greater than one.");

    // Calculate the rewards for the individual provers.
    for partial_solution in partial_solutions {
        // Compute the numerator.
        let numerator = (coinbase_reward as u128)
            .checked_mul(partial_solution.to_target()? as u128)
            .ok_or_else(|| anyhow!("Proving reward numerator overflowed"))?
            .checked_mul(remaining_coinbase_target as u128)
            .ok_or_else(|| anyhow!("Proving reward numerator overflowed"))?;
        // Compute the denominator.
        let denominator = combined_proof_target
            .checked_mul(2)
            .ok_or_else(|| anyhow!("Proving reward denominator overflowed"))?
            .checked_mul(coinbase_target as u128)
            .ok_or_else(|| anyhow!("Proving reward denominator overflowed"))?;
        // Compute the quotient.
        let quotient =
            numerator.checked_div(denominator).ok_or_else(|| anyhow!("Proving reward quotient overflowed"))?;

        // Cast the proving reward as a u64.
        let prover_reward = u64::try_from(quotient)?;
        // Ensure the proving reward is within a safe bound.
        ensure!(prover_reward <= 1_000_000_000, "Prover reward is too large");
        // Append the proving reward to the vector.
        proving_rewards.push(Ratify::ProvingReward(partial_solution.address(), prover_reward));
    }

    // Return the proving rewards.
    Ok(proving_rewards)
}
