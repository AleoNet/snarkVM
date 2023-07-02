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
use synthesizer::coinbase::ProverSolution;

use anyhow::Result;

/// Returns the proving rewards for a given coinbase reward and list of prover solutions.
///
/// The prover reward is defined as:
///   1/2 * coinbase_reward * (prover_target / cumulative_prover_target)
///   = (coinbase_reward * prover_target) / (2 * cumulative_prover_target)
pub fn proving_rewards<N: Network>(
    prover_solutions: Vec<ProverSolution<N>>,
    coinbase_reward: u64,
    cumulative_proof_target: u128,
) -> Result<Vec<Ratify<N>>> {
    // Initialize a vector to store the proving rewards.
    let mut proving_rewards = Vec::with_capacity(prover_solutions.len());

    // Calculate the rewards for the individual provers.
    for prover_solution in prover_solutions {
        // Compute the numerator.
        let numerator = (coinbase_reward as u128)
            .checked_mul(prover_solution.to_target()? as u128)
            .ok_or_else(|| anyhow!("Proving reward numerator overflowed"))?;
        // Compute the denominator.
        let denominator =
            cumulative_proof_target.checked_mul(2).ok_or_else(|| anyhow!("Proving reward denominator overflowed"))?;
        // Compute the quotient.
        let quotient =
            numerator.checked_div(denominator).ok_or_else(|| anyhow!("Proving reward quotient overflowed"))?;

        // Cast the proving reward as a u64.
        let prover_reward = u64::try_from(quotient)?;
        // Ensure the proving reward is within a safe bound.
        ensure!(prover_reward <= 1_000_000_000, "Prover reward is too large");
        // Append the proving reward to the vector.
        proving_rewards.push(Ratify::ProvingReward(prover_solution.address(), prover_reward));
    }

    // Return the proving rewards.
    Ok(proving_rewards)
}
