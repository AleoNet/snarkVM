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

/// A helper method to compute the proving reward for a given proof target, coinbase reward, combined proof target, remaining coinbase target, and coinbase target.
fn proving_reward(
    proof_target: u64,
    coinbase_reward: u64,
    combined_proof_target: u128,
    remaining_coinbase_target: u64,
    coinbase_target: u64,
) -> Result<u64> {
    // Compute the numerator.
    let numerator = (coinbase_reward as u128)
        .checked_mul(proof_target as u128)
        .ok_or_else(|| anyhow!("Proving reward numerator overflowed"))?;
    // Compute the denominator.
    let denominator =
        combined_proof_target.checked_mul(2).ok_or_else(|| anyhow!("Proving reward denominator overflowed"))?;
    // Compute the quotient.
    let quotient = numerator.checked_div(denominator).ok_or_else(|| anyhow!("Proving reward quotient overflowed"))?;

    // Calculate the reward scaled the the remaining coinbase target.
    let scaled_reward = quotient
        .checked_mul(remaining_coinbase_target as u128)
        .ok_or_else(|| anyhow!("Proving reward numerator overflowed"))?
        .checked_div(coinbase_target as u128)
        .ok_or_else(|| anyhow!("Proving reward denominator overflowed"))?;

    // Cast the proving reward as a u64.
    let prover_reward = u64::try_from(scaled_reward)?;
    // Ensure the proving reward is within a safe bound.
    ensure!(prover_reward <= 1_000_000_000, "Prover reward is too large");

    Ok(prover_reward)
}

/// Returns the proving rewards for a given coinbase reward, list of partial prover solutions, accumulated proof target, and coinbase target.
///
/// The prover reward is defined as:
///   1/2 * coinbase_reward * (prover_target / combined_proof_target) * ((coinbase_target - accumulated_proof_target) / coinbase_target)
///   = 1/2 * coinbase_reward * (prover_target / combined_proof_target) * (remaining_coinbase_target / coinbase_target)
///   = (coinbase_reward * prover_target) / (2  * coinbase_target) * (remaining_coinbase_target / coinbase_target)
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
        // Compute the proof target.
        let proof_target = partial_solution.to_target()?;
        // Compute the prover reward.
        let prover_reward = proving_reward(
            proof_target,
            coinbase_reward,
            combined_proof_target,
            remaining_coinbase_target,
            coinbase_target,
        )?;
        // Append the proving reward to the vector.
        proving_rewards.push(Ratify::ProvingReward(partial_solution.address(), prover_reward));
    }

    // Return the proving rewards.
    Ok(proving_rewards)
}

#[cfg(test)]
mod tests {
    use super::*;

    const ITERATIONS: usize = 1000;

    #[test]
    fn test_proving_rewards() {
        let rng = &mut TestRng::default();

        for _ in 0..ITERATIONS {
            // Initialize the total rewards paid out since the last coinbase target was reached.
            let mut total_rewards = 0;

            // Sample the base coinbase reward.
            let coinbase_reward: u64 = rng.gen_range(1_000_000..1_000_000_000);

            // Sample the coinbase target.
            let coinbase_target: u64 = rng.gen_range(1_000_000..100_000_000_000_000);

            // Initialize the accumulated proof target for this round.
            let mut accumulated_proof_target = 0;

            // Sample proof targets until the accumulated proof target is greater than the coinbase target.
            while accumulated_proof_target <= coinbase_target {
                // Sample the proof targets for this round.
                let proof_targets: Vec<u64> = (0..10).map(|_| rng.gen_range(1..coinbase_target)).collect();

                // Calculate the combined proof target and remaining coinbase target.
                let combined_proof_target = proof_targets.iter().map(|target| *target as u128).sum();
                let remaining_coinbase_target = coinbase_target.checked_sub(accumulated_proof_target).unwrap();

                // Calculate the remaining rewards for the current coinbase round.
                let remaining_payout = ((coinbase_reward as u128).saturating_sub(2))
                    .saturating_mul(remaining_coinbase_target as u128)
                    .saturating_div(coinbase_target as u128);

                for proof_target in proof_targets {
                    // Sample the reward for this prover.
                    let proving_reward = proving_reward(
                        proof_target,
                        coinbase_reward,
                        combined_proof_target,
                        remaining_coinbase_target,
                        coinbase_target,
                    )
                    .unwrap();
                    // Ensure that the proving reward is less than the remaining payout.
                    assert!(proving_reward as u128 <= remaining_payout);

                    total_rewards += proving_reward;
                }
                // Update the accumulated proof target.
                accumulated_proof_target =
                    accumulated_proof_target.saturating_add(u64::try_from(combined_proof_target).unwrap());
            }

            // Check that the total rewards paid out until accumulated proof target reaches the coinbase target is less than the coinbase reward.
            assert!(total_rewards <= coinbase_reward.saturating_sub(2));
        }
    }

    #[test]
    fn test_proving_rewards_with_large_proof_targets() {
        let rng = &mut TestRng::default();

        for _ in 0..ITERATIONS {
            // Initialize the total rewards paid out since the last coinbase target was reached.
            let mut total_rewards = 0;

            // Sample the base coinbase reward.
            let coinbase_reward: u64 = rng.gen_range(1_000_000..1_000_000_000);

            // Sample the coinbase target.
            let coinbase_target: u64 = rng.gen_range(1_000_000..10_000_000_000_000);

            // Initialize the accumulated proof target for this round.
            let mut accumulated_proof_target = 0;

            // Sample proof targets until the accumulated proof target is greater than the coinbase target.
            while accumulated_proof_target <= coinbase_target {
                // Sample the large proof target
                let large_proof_target: u64 = rng.gen_range(coinbase_target..u64::MAX / 2048);
                // Sample the proof targets for this round.
                let mut proof_targets: Vec<u64> = (0..10).map(|_| rng.gen_range(1..coinbase_target)).collect();
                // Add the large proof target to the proof targets.
                proof_targets.push(large_proof_target);

                // Calculate the combined proof target and remaining coinbase target.
                let combined_proof_target = proof_targets.iter().map(|target| *target as u128).sum();
                let remaining_coinbase_target = coinbase_target.checked_sub(accumulated_proof_target).unwrap();

                // Calculate the remaining rewards for the current coinbase round.
                let remaining_payout = ((coinbase_reward as u128).saturating_sub(2))
                    .saturating_mul(remaining_coinbase_target as u128)
                    .saturating_div(coinbase_target as u128);

                for proof_target in proof_targets {
                    // Sample the reward for this prover.
                    let proving_reward = proving_reward(
                        proof_target,
                        coinbase_reward,
                        combined_proof_target,
                        remaining_coinbase_target,
                        coinbase_target,
                    )
                    .unwrap();
                    // Ensure that the proving reward is less than the remaining payout.
                    assert!(proving_reward as u128 <= remaining_payout);

                    // Add the proving reward to the total rewards.
                    total_rewards += proving_reward;
                }

                // Update the accumulated proof target.
                accumulated_proof_target =
                    accumulated_proof_target.saturating_add(u64::try_from(combined_proof_target).unwrap());
            }

            // Check that the total rewards paid out until accumulated proof target reaches the coinbase target is less than `coinbase reward / 2`.
            assert!(total_rewards <= coinbase_reward.saturating_sub(2));
        }
    }
}
