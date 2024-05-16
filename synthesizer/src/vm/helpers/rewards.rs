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

use console::{account::Address, network::prelude::*};
use ledger_committee::{Committee, MIN_DELEGATOR_STAKE};

use indexmap::IndexMap;

#[cfg(not(feature = "serial"))]
use rayon::prelude::*;

/// A safety bound (sanity-check) for the coinbase reward.
const MAX_COINBASE_REWARD: u64 = ledger_block::MAX_COINBASE_REWARD; // Coinbase reward at block 1.

/// Returns the updated stakers reflecting the staking rewards for the given committee and block reward.
/// The staking reward is defined as: `block_reward * stake / total_stake`.
///
/// This method ensures that stakers who are bonded to validators with more than **25%**
/// of the total stake will not receive a staking reward. In addition, this method
/// ensures stakers who have less than 10 credit are not eligible for a staking reward.
///
/// The choice of 25% is to ensure at least 4 validators are operational at any given time,
/// since our security model adheres to 3f+1, where f=1. As such, we tolerate Byzantine behavior
/// up to 33% of the total stake.
pub fn staking_rewards<N: Network>(
    stakers: &IndexMap<Address<N>, (Address<N>, u64)>,
    committee: &Committee<N>,
    block_reward: u64,
) -> IndexMap<Address<N>, (Address<N>, u64)> {
    // If the list of stakers is empty, there is no stake, or the block reward is 0, return the stakers.
    if stakers.is_empty() || committee.total_stake() == 0 || block_reward == 0 {
        return stakers.clone();
    }

    // Create a map to track the commissions for each validator.
    let mut commissions: IndexMap<Address<N>, u64> = IndexMap::new();

    // Create a map to hold the updated stakers.
    let mut updated_stakers: IndexMap<Address<N>, (Address<N>, u64)> = IndexMap::new();

    // Iterate over the stakers to compute rewards and commissions.
    for (staker, (validator, stake)) in stakers.iter() {
        // If the validator is not in the committee, skip the staker.
        let validator_data = match committee.members().get(validator) {
            Some(data) => data,
            None => {
                trace!("Validator {validator} is not in the committee - skipping {staker}");
                updated_stakers.insert(*staker, (*validator, *stake));
                continue;
            }
        };

        let (validator_stake, _is_active, commission_rate) = *validator_data;

        // If the validator has more than 25% of the total stake, skip the staker.
        if validator_stake > committee.total_stake().saturating_div(4) {
            trace!("Validator {validator} has more than 25% of the total stake - skipping {staker}");
            updated_stakers.insert(*staker, (*validator, *stake));
            continue;
        }

        // If the staker has less than the minimum required stake, skip the staker.
        if *stake < MIN_DELEGATOR_STAKE {
            trace!("Staker has less than {MIN_DELEGATOR_STAKE} microcredits - skipping {staker}");
            updated_stakers.insert(*staker, (*validator, *stake));
            continue;
        }

        // Compute the numerator.
        let numerator = (block_reward as u128).saturating_mul(*stake as u128);
        // Compute the denominator.
        // Note: We guarantee this denominator cannot be 0 (as we return early if the total stake is 0).
        let denominator = committee.total_stake() as u128;
        // Compute the quotient.
        let quotient = numerator.saturating_div(denominator);
        // Ensure the staking reward is within a safe bound.
        if quotient > MAX_COINBASE_REWARD as u128 {
            error!("Staking reward ({quotient}) is too large - skipping {staker}");
            updated_stakers.insert(*staker, (*validator, *stake));
            continue;
        }
        // Cast the staking reward as a u64.
        // Note: This '.expect' is guaranteed to be safe, as we ensure the quotient is within a safe bound.
        let staking_reward = u64::try_from(quotient).expect("Staking reward is too large");

        // Compute the commission for the validator.
        let commission = (staking_reward as u128)
            .saturating_mul(commission_rate as u128)
            .saturating_div(100) as u64;

        // Update the commission for the validator.
        *commissions.entry(*validator).or_insert(0) += commission;

        // Compute the reward after commission.
        let reward_after_commission = staking_reward.saturating_sub(commission);

        // Update the staker's stake with the reward after commission.
        let updated_staker_stake = stake.saturating_add(reward_after_commission);

        // Insert the staker and the updated stake.
        updated_stakers.insert(*staker, (*validator, updated_staker_stake));
    }

    // Update the stakes for validators with their accumulated commissions.
    let mut final_stakers = updated_stakers.clone();
    for (validator, commission) in commissions {
        let (_, stake) = updated_stakers.get(&validator).unwrap_or_else(|| {
            error!("Validator {validator} is not self bonded - skipping commission");
            &updated_stakers.values().next().unwrap()
        });

        final_stakers.insert(validator, (validator, stake.saturating_add(commission)));
    }

    final_stakers
}

/// Returns the proving rewards for a given coinbase reward and list of prover solutions.
/// The prover reward is defined as: `puzzle_reward * (proof_target / combined_proof_target)`.
pub fn proving_rewards<N: Network>(
    proof_targets: Vec<(Address<N>, u64)>,
    puzzle_reward: u64,
) -> IndexMap<Address<N>, u64> {
    // Compute the combined proof target. Using '.sum' here is safe because we sum u64s into a u128.
    let combined_proof_target = proof_targets.iter().map(|(_, t)| *t as u128).sum::<u128>();

    // If the list of solutions is empty, the combined proof target is 0, or the puzzle reward is 0, return an empty map.
    if proof_targets.is_empty() || combined_proof_target == 0 || puzzle_reward == 0 {
        return Default::default();
    }

    // Initialize a vector to store the proving rewards.
    let mut rewards = IndexMap::<_, u64>::with_capacity(proof_targets.len());

    // Calculate the rewards for the individual provers.
    for (address, proof_target) in proof_targets {
        // Compute the numerator.
        let numerator = (puzzle_reward as u128).saturating_mul(proof_target as u128);
        // Compute the denominator.
        // Note: We guarantee this denominator cannot be 0 (to prevent a div by 0).
        let denominator = combined_proof_target.max(1);
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
            // Add the proving reward to the prover.
            let entry = rewards.entry(address).or_default();
            *entry = entry.saturating_add(prover_reward);
        }
    }

    // Return the proving rewards.
    rewards
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::prelude::TestRng;

    use indexmap::indexmap;

    type CurrentNetwork = console::network::MainnetV0;

    const ITERATIONS: usize = 1000;

    #[test]
    fn test_staking_rewards() {
        let rng = &mut TestRng::default();
        // Sample a random committee.
        let committee = ledger_committee::test_helpers::sample_committee(rng);
        // Sample a random block reward.
        let block_reward = rng.gen_range(0..MAX_COINBASE_REWARD);
        // Retrieve an address.
        let address = *committee.members().iter().next().unwrap().0;

        for _ in 0..ITERATIONS {
            // Sample a random stake.
            let stake = rng.gen_range(MIN_DELEGATOR_STAKE..committee.total_stake());
            // Construct the stakers.
            let stakers = indexmap! {address => (address, stake)};
            let next_stakers = staking_rewards::<CurrentNetwork>(&stakers, &committee, block_reward);
            assert_eq!(next_stakers.len(), 1);
            let (candidate_address, (candidate_validator, candidate_stake)) = next_stakers.into_iter().next().unwrap();
            assert_eq!(candidate_address, address);
            assert_eq!(candidate_validator, address);
            let reward = block_reward as u128 * stake as u128 / committee.total_stake() as u128;
            assert_eq!(candidate_stake, stake + u64::try_from(reward).unwrap(), "stake: {stake}, reward: {reward}");
        }
    }

    #[test]
    fn test_staking_rewards_to_validator_not_in_committee() {
        let rng = &mut TestRng::default();
        // Sample a random committee.
        let committee = ledger_committee::test_helpers::sample_committee(rng);
        let fake_committee = ledger_committee::test_helpers::sample_committee(rng);
        // Sample a random block reward.
        let block_reward = rng.gen_range(0..MAX_COINBASE_REWARD);

        // Generate the stakers
        let stakers = crate::committee::test_helpers::to_stakers(committee.members(), rng);
        // Generate stakers for a non-existent committee, to ensure they are not rewarded.
        let stakers_fake = crate::committee::test_helpers::to_stakers(fake_committee.members(), rng);
        let all_stakers: IndexMap<Address<CurrentNetwork>, (Address<CurrentNetwork>, u64)> = stakers.clone().into_iter().chain(stakers_fake.clone().into_iter()).collect();

        // Start a timer.
        let timer = std::time::Instant::now();

        let next_stakers = staking_rewards::<CurrentNetwork>(&all_stakers, &committee, block_reward);
        println!("staking_rewards: {}ms", timer.elapsed().as_millis());
        assert_eq!(next_stakers.len(), all_stakers.len());
        for ((staker, (validator, stake)), (next_staker, (next_validator, next_stake))) in
            all_stakers.into_iter().zip(next_stakers.into_iter())
        {
            assert_eq!(staker, next_staker);
            assert_eq!(validator, next_validator);
            // If the validator is not in the committee, the stake should not change.
            if !committee.members().contains_key(&validator) {
                assert_eq!(stake, next_stake, "stake: {stake}, reward should be 0");
            } else { // Otherwise, the stake should increase.
                let reward = block_reward as u128 * stake as u128 / committee.total_stake() as u128;
                assert_eq!(stake + u64::try_from(reward).unwrap(), next_stake, "stake: {stake}, reward: {reward}");
            }
        }
    }

    #[test]
    fn test_staking_rewards_large() {
        let rng = &mut TestRng::default();

        // Sample a random block reward.
        let block_reward = rng.gen_range(0..MAX_COINBASE_REWARD);
        // Sample a committee.
        let committee = ledger_committee::test_helpers::sample_committee_for_round_and_size(1, 100, rng);
        // Convert the committee into stakers.
        let stakers = crate::committee::test_helpers::to_stakers(committee.members(), rng);

        // Start a timer.
        let timer = std::time::Instant::now();
        // Compute the staking rewards.
        let next_stakers = staking_rewards::<CurrentNetwork>(&stakers, &committee, block_reward);
        println!("staking_rewards: {}ms", timer.elapsed().as_millis());
        assert_eq!(next_stakers.len(), stakers.len());
        for ((staker, (validator, stake)), (next_staker, (next_validator, next_stake))) in
            stakers.into_iter().zip(next_stakers.into_iter())
        {
            assert_eq!(staker, next_staker);
            assert_eq!(validator, next_validator);
            let reward = block_reward as u128 * stake as u128 / committee.total_stake() as u128;
            assert_eq!(stake + u64::try_from(reward).unwrap(), next_stake, "stake: {stake}, reward: {reward}");
        }
    }

    #[test]
    fn test_staking_rewards_when_staker_is_under_min_yields_no_reward() {
        let rng = &mut TestRng::default();
        // Sample a random committee.
        let committee = ledger_committee::test_helpers::sample_committee(rng);
        // Sample a random block reward.
        let block_reward = rng.gen_range(0..MAX_COINBASE_REWARD);
        // Retrieve an address.
        let address = *committee.members().iter().next().unwrap().0;

        for _ in 0..ITERATIONS {
            // Sample a random stake.
            let stake = rng.gen_range(0..MIN_DELEGATOR_STAKE);
            // Construct the stakers.
            let stakers = indexmap! {address => (address, stake)};
            let next_stakers = staking_rewards::<CurrentNetwork>(&stakers, &committee, block_reward);
            assert_eq!(next_stakers.len(), 1);
            let (candidate_address, (candidate_validator, candidate_stake)) = next_stakers.into_iter().next().unwrap();
            assert_eq!(candidate_address, address);
            assert_eq!(candidate_validator, address);
            assert_eq!(candidate_stake, stake);
        }
    }

    #[test]
    fn test_staking_rewards_cannot_exceed_coinbase_reward() {
        let rng = &mut TestRng::default();
        // Sample a random committee.
        let committee = ledger_committee::test_helpers::sample_committee(rng);
        // Retrieve an address.
        let address = *committee.members().iter().next().unwrap().0;

        // Construct the stakers.
        let stakers = indexmap![address => (address, MIN_DELEGATOR_STAKE)];
        // Check that a maxed out coinbase reward, returns empty.
        let next_stakers = staking_rewards::<CurrentNetwork>(&stakers, &committee, u64::MAX);
        assert_eq!(stakers, next_stakers);

        // Ensure a staking reward that is too large, renders no rewards.
        for _ in 0..ITERATIONS {
            // Sample a random overly-large block reward.
            let block_reward = rng.gen_range(MAX_COINBASE_REWARD..u64::MAX);
            // Sample a random stake.
            let stake = rng.gen_range(MIN_DELEGATOR_STAKE..u64::MAX);
            // Construct the stakers.
            let stakers = indexmap![address => (address, stake)];
            // Check that an overly large block reward fails.
            let next_stakers = staking_rewards::<CurrentNetwork>(&stakers, &committee, block_reward);
            assert_eq!(stakers, next_stakers);
        }
    }

    #[test]
    fn test_staking_rewards_is_empty() {
        let rng = &mut TestRng::default();
        // Sample a random committee.
        let committee = ledger_committee::test_helpers::sample_committee(rng);

        // Compute the staking rewards (empty).
        let rewards = staking_rewards::<CurrentNetwork>(&indexmap![], &committee, rng.gen());
        assert!(rewards.is_empty());
    }

    #[test]
    fn test_proving_rewards() {
        let rng = &mut TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a random address.
            let address = Address::rand(rng);
            // Sample a random puzzle reward.
            let puzzle_reward = rng.gen_range(0..MAX_COINBASE_REWARD);

            let rewards = proving_rewards::<CurrentNetwork>(vec![(address, u64::MAX)], puzzle_reward);
            assert_eq!(rewards.len(), 1);
            let (candidate_address, candidate_amount) = rewards.into_iter().next().unwrap();
            assert_eq!(candidate_address, address);
            assert!(candidate_amount <= puzzle_reward);
        }
    }

    #[test]
    fn test_proving_rewards_cannot_exceed_coinbase_reward() {
        let rng = &mut TestRng::default();

        // Ensure a proving reward that is too large, renders no rewards.
        for _ in 0..ITERATIONS {
            // Sample a random address.
            let address = Address::rand(rng);
            // Sample a random overly-large puzzle reward.
            let puzzle_reward = rng.gen_range(MAX_COINBASE_REWARD..u64::MAX);
            // Sample a random proof target.
            let proof_target = rng.gen_range(0..u64::MAX);
            // Check that a maxed out proof target fails.
            let rewards = proving_rewards::<CurrentNetwork>(vec![(address, proof_target)], puzzle_reward);
            assert!(rewards.is_empty());
        }
    }

    #[test]
    fn test_proving_rewards_is_empty() {
        let rng = &mut TestRng::default();
        // Sample a random address.
        let address = Address::rand(rng);

        // Compute the proving rewards (empty).
        let rewards = proving_rewards::<CurrentNetwork>(vec![], rng.gen());
        assert!(rewards.is_empty());

        // Check that a maxed out coinbase reward, returns empty.
        let rewards = proving_rewards::<CurrentNetwork>(vec![(address, 2)], u64::MAX);
        assert!(rewards.is_empty());

        // Ensure a 0 coinbase reward case is empty.
        let rewards = proving_rewards::<CurrentNetwork>(vec![(address, 2)], 0);
        assert!(rewards.is_empty());
    }
}
