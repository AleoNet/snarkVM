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

use crate::helpers::{block_reward, MAX_COINBASE_REWARD};
use console::{account::Address, network::prelude::*};
use ledger_block::{ConfirmedTransaction, Ratify};

use indexmap::IndexMap;

/// Returns the staking rewards for a given stakers and coinbase reward.
///
/// The staking reward is defined as:
///   block_reward * stake / total_stake
pub fn staking_rewards<'a, N: Network>(
    mut stakers: IndexMap<Address<N>, u64>,
    coinbase_reward: u64,
    confirmed_transactions: impl Iterator<Item = &'a ConfirmedTransaction<N>>,
) -> Vec<Ratify<N>> {
    // Filter the confirmed transactions down to the bond and unbond transitions.
    let bonds_and_unbonds = confirmed_transactions
        .filter_map(|transaction| {
            // Note: Leave this explicit, optimizers begone.
            match transaction {
                ConfirmedTransaction::AcceptedExecute(_, transaction, _) => Some(transaction),
                ConfirmedTransaction::AcceptedDeploy(..)
                | ConfirmedTransaction::RejectedDeploy(..)
                | ConfirmedTransaction::RejectedExecute(..) => None,
            }
        })
        .flat_map(|transaction| {
            transaction.transitions().filter(|transition| transition.is_bond() || transition.is_unbond())
        });

    // Update the stake of each staker based on the bond and unbond transitions.
    for transition in bonds_and_unbonds {
        // TODO (howardwu): Simulate the bond and unbond computations.
        //  Test: unbond, unbond+unbond, bond, bond+unbond, bond+unbond+bond, bond+unbond+unbond, etc.
        // if transition.is_bond() {
        //     let stake = stakers.get_mut(transition.address()).unwrap();
        //     *stake = stake.saturating_add(transition.amount());
        // } else if transition.is_unbond() {
        //     let stake = stakers.get_mut(transition.address()).unwrap();
        //     *stake = stake.saturating_sub(transition.amount());
        // }
    }

    // Filter the list of stakers to only include those with a stake.
    let stakers = stakers.into_iter().filter(|(_, s)| *s > 0).collect::<IndexMap<_, _>>();

    // Compute the total stake for the stakers.
    let mut total_stake = 0u64;
    for (_, stake) in &stakers {
        total_stake = total_stake.saturating_add(*stake);
    }

    // If the list of stakers is empty or there is no stake, return an empty vector.
    if stakers.is_empty() || total_stake == 0 {
        return Vec::new();
    }

    // Compute the block reward.
    let block_reward = block_reward(N::STARTING_SUPPLY, N::BLOCK_TIME, coinbase_reward);

    // Initialize a vector to store the staking rewards.
    let mut rewards = Vec::with_capacity(stakers.len());

    // Calculate the rewards for the individual stakers.
    for (address, stake) in stakers {
        // Compute the numerator.
        let numerator = (block_reward as u128).saturating_mul(stake as u128);
        // Compute the denominator.
        // Note: We guarantee this denominator cannot be 0 (as we return early if the total stake is 0).
        let denominator = total_stake as u128;
        // Compute the quotient.
        let quotient = numerator.saturating_div(denominator);
        // Ensure the staking reward is within a safe bound.
        if quotient > MAX_COINBASE_REWARD as u128 {
            error!("Staking reward ({quotient}) is too large - skipping {address}");
            continue;
        }
        // Cast the staking reward as a u64.
        // Note: This '.expect' is guaranteed to be safe, as we ensure the quotient is within a safe bound.
        let staking_reward = u64::try_from(quotient).expect("Staking reward is too large");
        // Add the staking reward to the list of rewards.
        rewards.push(Ratify::StakingReward(address, staking_reward));
    }

    // Return the proving rewards.
    rewards
}

/// Returns the proving rewards for a given coinbase reward and list of prover solutions.
///
/// The prover reward is defined as:
///   1/2 * coinbase_reward * (proof_target / combined_proof_target)
///   = (coinbase_reward * proof_target) / (2 * combined_proof_target)
pub fn proving_rewards<N: Network>(
    proof_targets: Vec<(Address<N>, u128)>,
    coinbase_reward: u64,
    combined_proof_target: u128,
) -> Vec<Ratify<N>> {
    // (Debug Mode) Ensure the combined proof target is equal to the sum of the proof targets.
    debug_assert_eq!(combined_proof_target, proof_targets.iter().map(|(_, t)| t).sum::<u128>());

    // If the list of solutions is empty, return an empty vector.
    if proof_targets.is_empty() {
        return Vec::new();
    }

    // Initialize a vector to store the proving rewards.
    let mut rewards = Vec::with_capacity(proof_targets.len());

    // Calculate the rewards for the individual provers.
    for (address, proof_target) in proof_targets {
        // Compute the numerator.
        let numerator = (coinbase_reward as u128).saturating_mul(proof_target);
        // Compute the denominator.
        // Note: We guarantee this denominator cannot be 0 (to prevent a div by 0).
        let denominator = combined_proof_target.saturating_mul(2).max(1);
        // Compute the quotient.
        let quotient = numerator.saturating_div(denominator);
        // Ensure the proving reward is within a safe bound.
        if quotient > MAX_COINBASE_REWARD as u128 {
            error!("Prover reward ({quotient}) is too large - skipping solution from {address}");
            continue;
        }
        // Cast the proving reward as a u64.
        // Note: This '.expect' is guaranteed to be safe, as we ensure the quotient is within a safe bound.
        let prover_reward = u64::try_from(quotient).expect("Prover reward is too large");
        // If there is a proving reward, append it to the vector.
        if prover_reward > 0 {
            // Append the proving reward to the vector.
            rewards.push(Ratify::ProvingReward(address, prover_reward));
        }
    }

    // Return the proving rewards.
    rewards
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::{prelude::TestRng, types::Group};

    use indexmap::indexmap;

    type CurrentNetwork = console::network::Testnet3;

    const ITERATIONS: usize = 1000;

    #[test]
    fn test_staking_rewards() {
        let rng = &mut TestRng::default();
        // Sample a random address.
        let address = Address::new(Group::rand(rng));

        // Ensure a 0 coinbase reward succeeds (i.e. post year 10 block reward simulation).
        let rewards = staking_rewards::<CurrentNetwork>(indexmap![address => 2], 0, [].iter());
        assert_eq!(rewards.len(), 1);
        assert!(matches!(rewards[0], Ratify::StakingReward(..)));
        if let Ratify::StakingReward(candidate_address, candidate_amount) = rewards[0] {
            // Compute the expected block reward.
            let block_reward = block_reward(CurrentNetwork::STARTING_SUPPLY, CurrentNetwork::BLOCK_TIME, 0);
            assert_eq!(candidate_address, address);
            assert_eq!(candidate_amount, block_reward);
        }
    }

    #[test]
    fn test_staking_rewards_cannot_exceed_coinbase_reward() {
        let rng = &mut TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a random address.
            let address = Address::new(Group::rand(rng));
            // Sample a random coinbase reward.
            let coinbase_reward = rng.gen_range(0..MAX_COINBASE_REWARD);

            let rewards = staking_rewards::<CurrentNetwork>(indexmap![address => u64::MAX], coinbase_reward, [].iter());
            assert_eq!(rewards.len(), 1);
            assert!(matches!(rewards[0], Ratify::StakingReward(..)));
            if let Ratify::StakingReward(candidate_address, candidate_amount) = rewards[0] {
                // Compute the expected block reward.
                let block_reward =
                    block_reward(CurrentNetwork::STARTING_SUPPLY, CurrentNetwork::BLOCK_TIME, coinbase_reward);
                assert_eq!(candidate_address, address);
                assert_eq!(candidate_amount, block_reward);
            }
        }
    }

    #[test]
    fn test_staking_rewards_is_empty() {
        let rng = &mut TestRng::default();
        // Sample a random address.
        let address = Address::new(Group::rand(rng));

        // Compute the staking rewards (empty).
        let rewards = staking_rewards::<CurrentNetwork>(indexmap![], rng.gen(), [].iter());
        assert!(rewards.is_empty());

        // Check that a maxed out coinbase reward, returns empty.
        let rewards = staking_rewards::<CurrentNetwork>(indexmap![address => 2], u64::MAX, [].iter());
        assert!(rewards.is_empty());

        // Ensure a staking reward that is too large, renders no rewards.
        for _ in 0..ITERATIONS {
            // Sample a random address.
            let address = Address::new(Group::rand(rng));
            // Sample a random overly-large coinbase reward.
            let coinbase_reward = rng.gen_range(MAX_COINBASE_REWARD..u64::MAX);
            // Sample a random stake.
            let stake = rng.gen_range(0..u64::MAX);
            // Check that an overly large coinbase reward fails.
            let rewards = staking_rewards::<CurrentNetwork>(indexmap![address => stake], coinbase_reward, [].iter());
            assert!(rewards.is_empty());
        }
    }

    #[test]
    fn test_proving_rewards_cannot_exceed_coinbase_reward() {
        let rng = &mut TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a random address.
            let address = Address::new(Group::rand(rng));
            // Sample a random coinbase reward.
            let coinbase_reward = rng.gen_range(0..MAX_COINBASE_REWARD);

            let rewards =
                proving_rewards::<CurrentNetwork>(vec![(address, u64::MAX as u128)], coinbase_reward, u64::MAX as u128);
            assert_eq!(rewards.len(), 1);
            assert!(matches!(rewards[0], Ratify::ProvingReward(..)));
            if let Ratify::ProvingReward(candidate_address, candidate_amount) = rewards[0] {
                assert_eq!(candidate_address, address);
                assert!(candidate_amount <= coinbase_reward);
            }
        }
    }

    #[test]
    fn test_proving_rewards_is_empty() {
        let rng = &mut TestRng::default();
        // Sample a random address.
        let address = Address::new(Group::rand(rng));

        // Compute the proving rewards (empty).
        let rewards = proving_rewards::<CurrentNetwork>(vec![], rng.gen(), 0);
        assert!(rewards.is_empty());

        // Check that a maxed out coinbase reward, returns empty.
        let rewards = proving_rewards::<CurrentNetwork>(vec![(address, 2)], u64::MAX, 2);
        assert!(rewards.is_empty());

        // Ensure a 0 coinbase reward case is empty.
        let rewards = proving_rewards::<CurrentNetwork>(vec![(address, 2)], 0, 2);
        assert!(rewards.is_empty());

        // Ensure a proving reward that is too large, renders no rewards.
        for _ in 0..ITERATIONS {
            // Sample a random address.
            let address = Address::new(Group::rand(rng));
            // Sample a random overly-large coinbase reward.
            let coinbase_reward = rng.gen_range(MAX_COINBASE_REWARD..u64::MAX);
            // Sample a random proof target.
            let proof_target = rng.gen_range(0..u64::MAX as u128);
            // Check that a maxed out proof target fails.
            let rewards =
                proving_rewards::<CurrentNetwork>(vec![(address, proof_target)], coinbase_reward, proof_target);
            assert!(rewards.is_empty());
        }
    }
}
