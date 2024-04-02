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

use console::prelude::{ensure, Network, Result};

/// A safety bound (sanity-check) for the coinbase reward.
pub const MAX_COINBASE_REWARD: u64 = 190_258_739; // Coinbase reward at block 1.

/// Calculate the block reward, given the total supply, block time, coinbase reward, and transaction fees.
///     R_staking = floor((0.05 * S) / H_Y1) + CR / 3 + TX_F.
///     S = Total supply.
///     H_Y1 = Expected block height at year 1.
///     CR = Coinbase reward.
///     TX_F = Transaction fees.
pub const fn block_reward(total_supply: u64, block_time: u16, coinbase_reward: u64, transaction_fees: u64) -> u64 {
    // Compute the expected block height at year 1.
    let block_height_at_year_1 = block_height_at_year(block_time, 1);
    // Compute the annual reward: (0.05 * S).
    let annual_reward = total_supply / 20;
    // Compute the block reward: (0.05 * S) / H_Y1.
    let block_reward = annual_reward / block_height_at_year_1 as u64;
    // Return the sum of the block reward, coinbase reward, and transaction fees.
    block_reward + (coinbase_reward / 3) + transaction_fees
}

/// Calculate the puzzle reward, given the coinbase reward.
pub const fn puzzle_reward(coinbase_reward: u64) -> u64 {
    // Return the coinbase reward multiplied by 2 and divided by 3.
    coinbase_reward.saturating_mul(2).saturating_div(3)
}

/// Calculates the coinbase reward for a given block.
///     R_coinbase = max(0, H_Y10 - H) * R_anchor * min(P, C_R) / C
///     R_anchor = Anchor reward.
///     H_Y10 = Anchor block height at year 10.
///     H = Current block height.
///     P = Combined proof target.
///     C_R = Remaining coinbase target.
///     C = Coinbase target.
pub fn coinbase_reward(
    block_height: u32,
    starting_supply: u64,
    anchor_height: u32,
    block_time: u16,
    combined_proof_target: u128,
    cumulative_proof_target: u64,
    coinbase_target: u64,
) -> Result<u64> {
    // Compute the remaining coinbase target.
    let remaining_coinbase_target = coinbase_target.saturating_sub(cumulative_proof_target);
    // Compute the remaining proof target.
    let remaining_proof_target = combined_proof_target.min(remaining_coinbase_target as u128);

    /* Until the anchor block height at year 10, the coinbase reward is determined by this equation: */
    /*   anchor_block_reward * remaining_proof_target / coinbase_target */

    // Compute the anchor block reward.
    let anchor_block_reward = anchor_block_reward_at_height(block_height, starting_supply, anchor_height, block_time);

    // Calculate the coinbase reward.
    let reward = anchor_block_reward.saturating_mul(remaining_proof_target).saturating_div(coinbase_target as u128);

    // Ensure the coinbase reward is less than the maximum coinbase reward.
    ensure!(reward <= MAX_COINBASE_REWARD as u128, "Coinbase reward ({reward}) exceeds maximum {MAX_COINBASE_REWARD}");

    // Return the coinbase reward.
    // Note: This '.expect' is guaranteed to be safe, as we ensure the reward is within a safe bound.
    Ok(u64::try_from(reward).expect("Coinbase reward exceeds u64::MAX"))
}

/// Calculates the anchor block reward for the given block height.
///     R_anchor = floor((2 * S * H_A * H_R) / (H_Y10 * (H_Y10 + 1))).
///     S = Starting supply.
///     H_A = Anchor block height.
///     H_R = Remaining number of blocks until year 10.
///     H_Y10 = Expected block height at year 10.
const fn anchor_block_reward_at_height(
    block_height: u32,
    starting_supply: u64,
    anchor_height: u32,
    block_time: u16,
) -> u128 {
    // Calculate the block height at year 10.
    let block_height_at_year_10 = block_height_at_year(block_time, 10) as u128;
    // Compute the remaining blocks until year 10, as a u64.
    let num_remaining_blocks_to_year_10 = block_height_at_year_10.saturating_sub(block_height as u128);
    // Compute the numerator.
    let numerator = 2 * starting_supply as u128 * anchor_height as u128 * num_remaining_blocks_to_year_10;
    // Compute the denominator.
    let denominator = block_height_at_year_10 * (block_height_at_year_10 + 1);
    // Return the anchor block reward.
    numerator / denominator
}

/// Returns the block height after a given number of years for a specific block time.
pub const fn block_height_at_year(block_time: u16, num_years: u32) -> u32 {
    // Calculate the number of seconds in a year.
    const SECONDS_IN_A_YEAR: u32 = 60 * 60 * 24 * 365;
    // Calculate the one-year block height.
    let block_height_at_year_1 = SECONDS_IN_A_YEAR / block_time as u32;
    // Return the block height for the given number of years.
    block_height_at_year_1 * num_years
}

/// Calculate the coinbase target for the given block timestamps and target.
pub fn coinbase_target(
    previous_target: u64,
    previous_block_timestamp: i64,
    block_timestamp: i64,
    anchor_time: u16,
    num_blocks_per_epoch: u32,
    genesis_target: u64,
) -> Result<u64> {
    // Compute the half life.
    let half_life = num_blocks_per_epoch.saturating_div(2).saturating_mul(anchor_time as u32);
    // Compute the new coinbase target.
    let candidate_target =
        retarget(previous_target, previous_block_timestamp, block_timestamp, anchor_time, half_life, true)?;
    // Return the new coinbase target, floored at the genesis target.
    Ok(candidate_target.max(genesis_target))
}

/// Calculate the minimum proof target for the given coinbase target.
pub fn proof_target(coinbase_target: u64, genesis_proof_target: u64, max_solutions_as_power_of_two: u8) -> u64 {
    coinbase_target
        .checked_shr(max_solutions_as_power_of_two as u32)
        .map(|target| target.saturating_add(1))
        .unwrap_or(genesis_proof_target)
}

/// Retarget algorithm using fixed point arithmetic from https://www.reference.cash/protocol/forks/2020-11-15-asert.
///     T_{i+1} = T_i * 2^(INV * (D - A) / TAU).
///     T_i = Current target.
///     D = Drift, defined as the number of blocks elapsed.
///     A = Anchor timestamp, defined as expected number of seconds elapsed.
///     TAU = Rate of doubling (or half-life) in seconds.
///     INV = {-1, 1} depending on whether the target is increasing or decreasing.
fn retarget(
    previous_target: u64,
    previous_block_timestamp: i64,
    block_timestamp: i64,
    anchor_time: u16,
    half_life: u32,
    is_inverse: bool,
) -> Result<u64> {
    // Determine the block time elapsed (in seconds) since the previous block.
    // Note: This operation includes a safety check for a repeat block timestamp.
    let block_time_elapsed = block_timestamp.saturating_sub(previous_block_timestamp).max(1);
    // Compute the drift.
    let mut drift = block_time_elapsed.saturating_sub(anchor_time as i64);

    // If the drift is zero, return the previous target.
    if drift == 0 {
        return Ok(previous_target);
    }

    // Negate the drift if the inverse flag is set.
    if is_inverse {
        drift *= -1;
    }

    // Constants used for fixed point arithmetic.
    const RBITS: u32 = 16;
    const RADIX: u128 = 1 << RBITS;

    // Compute the exponent factor, and decompose it into integral & fractional parts for fixed point arithmetic.
    let (integral, fractional) = {
        // Calculate the exponent factor.
        let exponent = (RADIX as i128).saturating_mul(drift as i128) / half_life as i128;

        // Decompose into the integral and fractional parts.
        let integral = exponent >> RBITS;
        let fractional = (exponent - (integral << RBITS)) as u128;
        ensure!(fractional < RADIX, "Fractional part is not within the fixed point size");
        ensure!(exponent == (integral * (RADIX as i128) + fractional as i128), "Exponent is decomposed incorrectly");

        (integral, fractional)
    };

    // Approximate the fractional multiplier as 2^RBITS * 2^fractional, where:
    // 2^x ~= (1 + 0.695502049*x + 0.2262698*x**2 + 0.0782318*x**3)
    let fractional_multiplier = RADIX
        + ((195_766_423_245_049_u128 * fractional
            + 971_821_376_u128 * fractional.pow(2)
            + 5_127_u128 * fractional.pow(3)
            + 2_u128.pow(RBITS * 3 - 1))
            >> (RBITS * 3));

    // Cast the previous coinbase target from a u64 to a u128.
    // The difficulty target must allow for leading zeros to account for overflows;
    // an additional 64-bits for the leading zeros suffices.
    let candidate_target = (previous_target as u128).saturating_mul(fractional_multiplier);

    // Calculate the new difficulty.
    // Shift the target to multiply by 2^(integer) / RADIX.
    let shifts = integral - RBITS as i128;
    let mut candidate_target = if shifts < 0 {
        match candidate_target.checked_shr(u32::try_from(-shifts)?) {
            Some(target) => core::cmp::max(target, 1),
            None => 1,
        }
    } else {
        match candidate_target.checked_shl(u32::try_from(shifts)?) {
            Some(target) => core::cmp::max(target, 1),
            None => u64::MAX as u128,
        }
    };

    // Cap the target at `u64::MAX` if it has overflowed.
    candidate_target = core::cmp::min(candidate_target, u64::MAX as u128);

    // Ensure that the leading 64 bits are zeros.
    ensure!(candidate_target.checked_shr(64) == Some(0), "The target has overflowed");
    // Cast the new target down from a u128 to a u64.
    Ok(u64::try_from(candidate_target)?)
}

/// This function calculates the next targets for the given attributes:
///     `latest_cumulative_proof_target`: The latest cumulative proof target.
///     `combined_proof_target`: The combined proof target of solutions in the block.
///     `latest_coinbase_target`: The latest coinbase target.
///     `last_coinbase_target`: The coinbase target for the last coinbase.
///     `last_coinbase_timestamp`: The timestamp for the last coinbase.
///     `next_timestamp`: The timestamp for the next block.
///
/// Returns the following as a tuple:
///     `next_coinbase_target` - The next coinbase target.
///     `next_proof_target` - The next proof target.
///     `next_cumulative_proof_target` - The next cumulative proof target.
///     `next_cumulative_weight` - The next cumulative weight.
///     `next_last_coinbase_target` - The next last coinbase target.
///     `next_last_coinbase_timestamp` - The next last coinbase timestamp.
pub fn to_next_targets<N: Network>(
    latest_cumulative_proof_target: u128,
    combined_proof_target: u128,
    latest_coinbase_target: u64,
    latest_cumulative_weight: u128,
    last_coinbase_target: u64,
    last_coinbase_timestamp: i64,
    next_timestamp: i64,
) -> Result<(u64, u64, u128, u128, u64, i64)> {
    // Compute the coinbase target threshold.
    let latest_coinbase_threshold = latest_coinbase_target.saturating_div(2) as u128;
    // Compute the next cumulative proof target.
    let next_cumulative_proof_target = latest_cumulative_proof_target.saturating_add(combined_proof_target);
    // Determine if the coinbase target threshold is reached.
    let is_coinbase_threshold_reached = next_cumulative_proof_target >= latest_coinbase_threshold;
    // Construct the next coinbase target.
    let next_coinbase_target = coinbase_target(
        last_coinbase_target,
        last_coinbase_timestamp,
        next_timestamp,
        N::ANCHOR_TIME,
        N::NUM_BLOCKS_PER_EPOCH,
        N::GENESIS_COINBASE_TARGET,
    )?;
    // Construct the next proof target.
    let next_proof_target =
        proof_target(next_coinbase_target, N::GENESIS_PROOF_TARGET, N::MAX_SOLUTIONS_AS_POWER_OF_TWO);

    // Update the next cumulative proof target, if necessary.
    let next_cumulative_proof_target = match is_coinbase_threshold_reached {
        true => 0,
        false => next_cumulative_proof_target,
    };

    // Compute the next cumulative weight.
    let next_cumulative_weight = latest_cumulative_weight.saturating_add(combined_proof_target);

    // Construct the next last coinbase target and next last coinbase timestamp.
    let (next_last_coinbase_target, next_last_coinbase_timestamp) = match is_coinbase_threshold_reached {
        true => (next_coinbase_target, next_timestamp),
        false => (last_coinbase_target, last_coinbase_timestamp),
    };

    Ok((
        next_coinbase_target,
        next_proof_target,
        next_cumulative_proof_target,
        next_cumulative_weight,
        next_last_coinbase_target,
        next_last_coinbase_timestamp,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::{prelude::*, MainnetV0};

    type CurrentNetwork = MainnetV0;

    const ITERATIONS: u32 = 1000;

    const EXPECTED_ANCHOR_BLOCK_REWARD_AT_BLOCK_1: u128 = MAX_COINBASE_REWARD as u128;
    const EXPECTED_STAKING_REWARD: u64 = 23_782_343;
    const EXPECTED_COINBASE_REWARD_AT_BLOCK_1: u64 = MAX_COINBASE_REWARD;

    #[test]
    fn test_anchor_block_reward() {
        let reward = anchor_block_reward_at_height(
            1,
            CurrentNetwork::STARTING_SUPPLY,
            CurrentNetwork::ANCHOR_HEIGHT,
            CurrentNetwork::BLOCK_TIME,
        );
        assert_eq!(reward, EXPECTED_ANCHOR_BLOCK_REWARD_AT_BLOCK_1);

        // Calculate the block height at year 10.
        let block_height_at_year_10 = block_height_at_year(CurrentNetwork::BLOCK_TIME, 10);

        // Ensure that the reward is decreasing for blocks before year 10.
        let mut previous_reward = reward;
        let anchor_height = CurrentNetwork::ANCHOR_HEIGHT as usize;
        for height in (2..block_height_at_year_10).step_by(anchor_height).skip(1) {
            let reward = anchor_block_reward_at_height(
                height,
                CurrentNetwork::STARTING_SUPPLY,
                CurrentNetwork::ANCHOR_HEIGHT,
                CurrentNetwork::BLOCK_TIME,
            );
            assert!(reward < previous_reward, "Failed on block height {height}");
            previous_reward = reward;
        }

        // Ensure that the reward is zero for blocks after year 10.
        for height in block_height_at_year_10..(block_height_at_year_10 + ITERATIONS) {
            let reward = anchor_block_reward_at_height(
                height,
                CurrentNetwork::STARTING_SUPPLY,
                CurrentNetwork::ANCHOR_HEIGHT,
                CurrentNetwork::BLOCK_TIME,
            );
            assert_eq!(reward, 0);
        }
    }

    #[test]
    fn test_block_reward() {
        let reward = block_reward(CurrentNetwork::STARTING_SUPPLY, CurrentNetwork::BLOCK_TIME, 0, 0);
        assert_eq!(reward, EXPECTED_STAKING_REWARD);

        // Increasing the anchor time will increase the reward.
        let larger_reward = block_reward(CurrentNetwork::STARTING_SUPPLY, CurrentNetwork::BLOCK_TIME + 1, 0, 0);
        assert!(reward < larger_reward);

        // Decreasing the anchor time will decrease the reward.
        let smaller_reward = block_reward(CurrentNetwork::STARTING_SUPPLY, CurrentNetwork::BLOCK_TIME - 1, 0, 0);
        assert!(reward > smaller_reward);
    }

    #[test]
    fn test_coinbase_reward() {
        let coinbase_target: u64 = 10000;
        let combined_proof_target: u128 = coinbase_target as u128;

        let reward = coinbase_reward(
            1,
            CurrentNetwork::STARTING_SUPPLY,
            CurrentNetwork::ANCHOR_HEIGHT,
            CurrentNetwork::BLOCK_TIME,
            combined_proof_target,
            0,
            coinbase_target,
        )
        .unwrap();
        assert_eq!(reward, EXPECTED_COINBASE_REWARD_AT_BLOCK_1);

        // Halving the combined proof target halves the reward.
        let smaller_reward = coinbase_reward(
            1,
            CurrentNetwork::STARTING_SUPPLY,
            CurrentNetwork::ANCHOR_HEIGHT,
            CurrentNetwork::BLOCK_TIME,
            combined_proof_target / 2,
            0,
            coinbase_target,
        )
        .unwrap();
        assert_eq!(smaller_reward, reward / 2);

        // Halving the remaining coinbase target halves the reward.
        let smaller_reward = coinbase_reward(
            1,
            CurrentNetwork::STARTING_SUPPLY,
            CurrentNetwork::ANCHOR_HEIGHT,
            CurrentNetwork::BLOCK_TIME,
            combined_proof_target,
            coinbase_target / 2,
            coinbase_target,
        )
        .unwrap();
        assert_eq!(smaller_reward, reward / 2);

        // Dramatically increasing the combined proof target greater than the remaining coinbase target will not increase the reward.
        let equivalent_reward = coinbase_reward(
            1,
            CurrentNetwork::STARTING_SUPPLY,
            CurrentNetwork::ANCHOR_HEIGHT,
            CurrentNetwork::BLOCK_TIME,
            u128::MAX,
            0,
            coinbase_target,
        )
        .unwrap();
        assert_eq!(reward, equivalent_reward);

        // Decreasing the combined proof target to 0 will result in a reward of 0.
        let zero_reward = coinbase_reward(
            1,
            CurrentNetwork::STARTING_SUPPLY,
            CurrentNetwork::ANCHOR_HEIGHT,
            CurrentNetwork::BLOCK_TIME,
            0,
            0,
            coinbase_target,
        )
        .unwrap();
        assert_eq!(zero_reward, 0);

        // Increasing the cumulative proof target beyond the coinbase target will result in a reward of 0.
        let zero_reward = coinbase_reward(
            1,
            CurrentNetwork::STARTING_SUPPLY,
            CurrentNetwork::ANCHOR_HEIGHT,
            CurrentNetwork::BLOCK_TIME,
            1,
            coinbase_target + 1,
            coinbase_target,
        )
        .unwrap();
        assert_eq!(zero_reward, 0);
    }

    #[test]
    fn test_coinbase_reward_remaining_target() {
        let mut rng = TestRng::default();

        fn compute_coinbase_reward(
            combined_proof_target: u64,
            cumulative_proof_target: u64,
            coinbase_target: u64,
        ) -> u64 {
            coinbase_reward(
                1,
                CurrentNetwork::STARTING_SUPPLY,
                CurrentNetwork::ANCHOR_HEIGHT,
                CurrentNetwork::BLOCK_TIME,
                combined_proof_target as u128,
                cumulative_proof_target,
                coinbase_target,
            )
            .unwrap()
        }

        // Sample the starting conditions.
        let coinbase_target: u64 = rng.gen_range(1_000_000..1_000_000_000_000_000);
        let cumulative_proof_target = coinbase_target / 2;
        let combined_proof_target = coinbase_target / 4;
        let reward = compute_coinbase_reward(combined_proof_target, cumulative_proof_target, coinbase_target);

        for _ in 0..ITERATIONS {
            // Check that as long as the sum of the combined proof target and cumulative proof target is less than the coinbase target,
            // the reward remains the same.
            // Intuition: Staying below the coinbase target preserves the reward for the combined proof target.
            let equivalent_reward = compute_coinbase_reward(
                combined_proof_target,
                rng.gen_range(0..(coinbase_target - combined_proof_target)),
                coinbase_target,
            );
            assert_eq!(reward, equivalent_reward);

            // Check that increasing the cumulative proof target to devalue the combined proof target will decrease the reward.
            // Intuition: Overflowing the coinbase target crowds out the combined proof target, leading to less reward for the combined proof target.
            let lower_reward = compute_coinbase_reward(
                combined_proof_target,
                rng.gen_range((coinbase_target - combined_proof_target + 1)..coinbase_target),
                coinbase_target,
            );
            assert!(lower_reward < reward);

            // Check that increasing the combined proof target increases the reward.
            // Intuition: If a prover contributes more proof target, they should be rewarded more.
            let larger_reward = compute_coinbase_reward(
                rng.gen_range(combined_proof_target + 1..u64::MAX),
                cumulative_proof_target,
                coinbase_target,
            );
            assert!(reward < larger_reward);
        }
    }

    #[test]
    fn test_coinbase_reward_up_to_year_10() {
        let block_height_at_year_10 = block_height_at_year(CurrentNetwork::BLOCK_TIME, 10);

        let mut block_height = 1;

        let mut previous_reward = coinbase_reward(
            block_height,
            CurrentNetwork::STARTING_SUPPLY,
            CurrentNetwork::ANCHOR_HEIGHT,
            CurrentNetwork::BLOCK_TIME,
            1,
            0,
            1,
        )
        .unwrap();

        block_height += 1;

        let mut total_reward = previous_reward;

        let coinbase_target = CurrentNetwork::ANCHOR_HEIGHT as u64;
        let mut cumulative_proof_target = 0;

        let mut hit_500m = false;
        let mut hit_1b = false;

        while block_height < block_height_at_year_10 {
            let reward = coinbase_reward(
                block_height,
                CurrentNetwork::STARTING_SUPPLY,
                CurrentNetwork::ANCHOR_HEIGHT,
                CurrentNetwork::BLOCK_TIME,
                1,
                cumulative_proof_target,
                coinbase_target,
            )
            .unwrap();
            assert!(reward <= previous_reward);

            total_reward += reward;
            previous_reward = reward;
            block_height += 1;

            // Update the cumulative proof target.
            cumulative_proof_target = match cumulative_proof_target + 1 {
                cumulative_proof_target if cumulative_proof_target == coinbase_target => 0,
                cumulative_proof_target => cumulative_proof_target,
            };

            if !hit_500m && total_reward > 500_000_000_000_000 {
                println!("500M credits block height is {block_height}");
                assert_eq!(block_height, 5_786_964, "Update me if my parameters have changed");
                hit_500m = true;
            } else if !hit_1b && total_reward > 1_000_000_000_000_000 {
                println!("1B credits block height is {block_height}");
                assert_eq!(block_height, 13_328_683, "Update me if my parameters have changed");
                hit_1b = true;
            }
        }

        assert_eq!(total_reward, 1_499_999_984_232_003, "Update me if my parameters have changed");
    }

    #[test]
    fn test_coinbase_reward_after_year_10() {
        let mut rng = TestRng::default();

        let block_height_at_year_10 = block_height_at_year(CurrentNetwork::BLOCK_TIME, 10);

        // Check that the block at year 10 has a reward of 0.
        let reward = coinbase_reward(
            block_height_at_year_10,
            CurrentNetwork::STARTING_SUPPLY,
            CurrentNetwork::ANCHOR_HEIGHT,
            CurrentNetwork::BLOCK_TIME,
            1,
            0,
            1,
        )
        .unwrap();
        assert_eq!(reward, 0);

        // Check that the subsequent blocks have a reward of 0.
        for _ in 0..ITERATIONS {
            let block_height: u32 = rng.gen_range(block_height_at_year_10..block_height_at_year_10 * 10);
            let coinbase_target = rng.gen_range(1_000_000..1_000_000_000_000_000);
            let cumulative_proof_target = rng.gen_range(0..coinbase_target);
            let combined_proof_target = rng.gen_range(0..coinbase_target as u128);

            let reward = coinbase_reward(
                block_height,
                CurrentNetwork::STARTING_SUPPLY,
                CurrentNetwork::ANCHOR_HEIGHT,
                CurrentNetwork::BLOCK_TIME,
                combined_proof_target,
                cumulative_proof_target,
                coinbase_target,
            )
            .unwrap();

            assert_eq!(reward, 0);
        }
    }

    #[test]
    fn test_targets() {
        let mut rng = TestRng::default();

        let minimum_coinbase_target: u64 = 2u64.pow(10) - 1;

        fn test_new_targets(rng: &mut TestRng, minimum_coinbase_target: u64) {
            let previous_coinbase_target: u64 = rng.gen_range(minimum_coinbase_target..u64::MAX);
            let previous_prover_target = proof_target(
                previous_coinbase_target,
                CurrentNetwork::GENESIS_PROOF_TARGET,
                CurrentNetwork::MAX_SOLUTIONS_AS_POWER_OF_TWO,
            );

            let previous_timestamp = rng.gen();

            // Targets stay the same when the drift is as expected.
            let next_timestamp = previous_timestamp + CurrentNetwork::ANCHOR_TIME as i64;
            let new_coinbase_target = coinbase_target(
                previous_coinbase_target,
                previous_timestamp,
                next_timestamp,
                CurrentNetwork::ANCHOR_TIME,
                CurrentNetwork::NUM_BLOCKS_PER_EPOCH,
                CurrentNetwork::GENESIS_COINBASE_TARGET,
            )
            .unwrap();
            let new_prover_target = proof_target(
                new_coinbase_target,
                CurrentNetwork::GENESIS_PROOF_TARGET,
                CurrentNetwork::MAX_SOLUTIONS_AS_POWER_OF_TWO,
            );
            assert_eq!(new_coinbase_target, previous_coinbase_target);
            assert_eq!(new_prover_target, previous_prover_target);

            // Targets decrease (easier) when the drift is greater than expected.
            let new_timestamp = previous_timestamp + 2 * CurrentNetwork::ANCHOR_TIME as i64;
            let new_coinbase_target = coinbase_target(
                previous_coinbase_target,
                previous_timestamp,
                new_timestamp,
                CurrentNetwork::ANCHOR_TIME,
                CurrentNetwork::NUM_BLOCKS_PER_EPOCH,
                CurrentNetwork::GENESIS_COINBASE_TARGET,
            )
            .unwrap();
            let new_prover_target = proof_target(
                new_coinbase_target,
                CurrentNetwork::GENESIS_PROOF_TARGET,
                CurrentNetwork::MAX_SOLUTIONS_AS_POWER_OF_TWO,
            );
            assert!(new_coinbase_target < previous_coinbase_target);
            assert!(new_prover_target < previous_prover_target);

            // Targets increase (harder) when the drift is less than expected.
            let next_timestamp = previous_timestamp + (CurrentNetwork::ANCHOR_TIME / 2) as i64;
            let new_coinbase_target = coinbase_target(
                previous_coinbase_target,
                previous_timestamp,
                next_timestamp,
                CurrentNetwork::ANCHOR_TIME,
                CurrentNetwork::NUM_BLOCKS_PER_EPOCH,
                CurrentNetwork::GENESIS_COINBASE_TARGET,
            )
            .unwrap();
            let new_prover_target = proof_target(
                new_coinbase_target,
                CurrentNetwork::GENESIS_PROOF_TARGET,
                CurrentNetwork::MAX_SOLUTIONS_AS_POWER_OF_TWO,
            );

            assert!(new_coinbase_target > previous_coinbase_target);
            assert!(new_prover_target > previous_prover_target);
        }

        for _ in 0..ITERATIONS {
            test_new_targets(&mut rng, minimum_coinbase_target);
        }
    }

    #[test]
    fn test_target_halving() {
        let mut rng = TestRng::default();

        let minimum_coinbase_target: u64 = 2u64.pow(10) - 1;

        for _ in 0..ITERATIONS {
            let previous_coinbase_target: u64 = rng.gen_range(minimum_coinbase_target..u64::MAX);
            let previous_timestamp = rng.gen();

            let half_life = CurrentNetwork::NUM_BLOCKS_PER_EPOCH
                .saturating_div(2)
                .saturating_mul(CurrentNetwork::ANCHOR_TIME as u32) as i64;

            // New coinbase target is greater than half if the drift equals the half life.
            let next_timestamp = previous_timestamp + half_life;
            let next_coinbase_target = coinbase_target(
                previous_coinbase_target,
                previous_timestamp,
                next_timestamp,
                CurrentNetwork::ANCHOR_TIME,
                CurrentNetwork::NUM_BLOCKS_PER_EPOCH,
                CurrentNetwork::GENESIS_COINBASE_TARGET,
            )
            .unwrap();

            assert!(next_coinbase_target > previous_coinbase_target / 2);

            // New coinbase target is halved if the drift is 1 anchor height past the half life.
            let next_timestamp = previous_timestamp + half_life + CurrentNetwork::ANCHOR_TIME as i64;
            let next_coinbase_target = coinbase_target(
                previous_coinbase_target,
                previous_timestamp,
                next_timestamp,
                CurrentNetwork::ANCHOR_TIME,
                CurrentNetwork::NUM_BLOCKS_PER_EPOCH,
                CurrentNetwork::GENESIS_COINBASE_TARGET,
            )
            .unwrap();

            assert_eq!(next_coinbase_target, previous_coinbase_target / 2);

            // New coinbase target is less than half if the drift is more than 1 anchor height past the half life.
            let next_timestamp = previous_timestamp + half_life + 2 * CurrentNetwork::ANCHOR_TIME as i64;
            let next_coinbase_target = coinbase_target(
                previous_coinbase_target,
                previous_timestamp,
                next_timestamp,
                CurrentNetwork::ANCHOR_TIME,
                CurrentNetwork::NUM_BLOCKS_PER_EPOCH,
                CurrentNetwork::GENESIS_COINBASE_TARGET,
            )
            .unwrap();

            assert!(next_coinbase_target < previous_coinbase_target / 2);
        }
    }

    #[test]
    fn test_target_doubling() {
        let mut rng = TestRng::default();

        // The custom block height drift that is faster than the anchor time.
        const ANCHOR_TIME_DELTA: i64 = 15;
        // The expected number of blocks before the coinbase target is doubled.
        const EXPECTED_NUM_BLOCKS_TO_DOUBLE: u32 = 451;

        let minimum_coinbase_target: u64 = 2u64.pow(10) - 1;

        let initial_coinbase_target: u64 = rng.gen_range(minimum_coinbase_target..u64::MAX / 2);
        let initial_timestamp: i64 = rng.gen();

        let mut previous_coinbase_target: u64 = initial_coinbase_target;
        let mut previous_timestamp = initial_timestamp;
        let mut num_blocks = 0;

        while previous_coinbase_target < initial_coinbase_target * 2 {
            // Targets increase (harder) when the timestamp is less than expected.
            let next_timestamp = previous_timestamp + ANCHOR_TIME_DELTA;
            let next_coinbase_target = coinbase_target(
                previous_coinbase_target,
                previous_timestamp,
                next_timestamp,
                CurrentNetwork::ANCHOR_TIME,
                CurrentNetwork::NUM_BLOCKS_PER_EPOCH,
                CurrentNetwork::GENESIS_COINBASE_TARGET,
            )
            .unwrap();

            assert!(next_coinbase_target > previous_coinbase_target);

            previous_coinbase_target = next_coinbase_target;
            previous_timestamp = next_timestamp;
            num_blocks += 1;
        }

        let seconds = previous_timestamp - initial_timestamp;
        println!(
            "For drifts of {ANCHOR_TIME_DELTA} seconds and epochs of {} blocks, doubling the coinbase target took {num_blocks} blocks. ({seconds} seconds)",
            CurrentNetwork::NUM_BLOCKS_PER_EPOCH,
        );

        assert_eq!(EXPECTED_NUM_BLOCKS_TO_DOUBLE, num_blocks);
    }

    #[test]
    fn test_to_next_targets_meets_threshold() {
        let mut rng = TestRng::default();

        let minimum_coinbase_target: u64 = 2u64.pow(10) - 1;

        for _ in 0..ITERATIONS {
            // Sample the initial values.
            let latest_coinbase_target = rng.gen_range(minimum_coinbase_target..u64::MAX / 2);
            let threshold = latest_coinbase_target as u128 / 2;
            let last_coinbase_target = rng.gen_range(minimum_coinbase_target..latest_coinbase_target);
            let last_coinbase_timestamp = rng.gen_range(0..i64::MAX / 2);
            let next_timestamp = last_coinbase_timestamp + 100;
            let latest_cumulative_weight = rng.gen_range(0..u128::MAX / 2);

            // Sample a cumulative proof target and combined proof target pair that meets the threshold.
            let latest_cumulative_proof_target = rng.gen_range(0..threshold);
            let combined_proof_target =
                rng.gen_range(threshold.saturating_sub(latest_cumulative_proof_target)..u128::MAX);

            assert!(latest_cumulative_proof_target.saturating_add(combined_proof_target) >= threshold);

            // Calculate the next targets.
            let (
                _,
                _,
                next_cumulative_proof_target,
                next_cumulative_weight,
                next_last_coinbase_target,
                next_last_coinbase_timestamp,
            ) = to_next_targets::<CurrentNetwork>(
                latest_cumulative_proof_target,
                combined_proof_target,
                latest_coinbase_target,
                latest_cumulative_weight,
                last_coinbase_target,
                last_coinbase_timestamp,
                next_timestamp,
            )
            .unwrap();

            // Check that meeting the target threshold does the following:
            // 1. Resets the next_cumulative_proof_target.
            // 2. Updates the last_coinbase_target.
            // 3. Updates the last_coinbase_timestamp.
            assert_eq!(next_cumulative_proof_target, 0);
            assert_ne!(next_last_coinbase_target, last_coinbase_target);
            assert_eq!(next_last_coinbase_timestamp, next_timestamp);

            // Check that the cumulative_weight is updated correctly.
            assert_eq!(next_cumulative_weight, latest_cumulative_weight.saturating_add(combined_proof_target));
        }
    }

    #[test]
    fn test_to_next_targets_does_not_meet_threshold() {
        let mut rng = TestRng::default();

        let minimum_coinbase_target: u64 = 2u64.pow(10) - 1;

        for _ in 0..ITERATIONS {
            // Sample the initial values.
            let latest_coinbase_target = rng.gen_range(minimum_coinbase_target..u64::MAX / 2);
            let threshold = latest_coinbase_target as u128 / 2;
            let last_coinbase_target = rng.gen_range(minimum_coinbase_target..latest_coinbase_target);
            let last_coinbase_timestamp = rng.gen_range(0..i64::MAX / 2);
            let next_timestamp = last_coinbase_timestamp + 100;
            let latest_cumulative_weight = rng.gen_range(0..u128::MAX / 2);

            // Sample a cumulative proof target and combined proof target pair that meets the threshold.
            let latest_cumulative_proof_target = rng.gen_range(0..threshold);
            let combined_proof_target = rng.gen_range(0..threshold.saturating_sub(latest_cumulative_proof_target));

            assert!(latest_cumulative_proof_target.saturating_add(combined_proof_target) < threshold);

            // Calculate the next targets.
            let (
                _,
                _,
                next_cumulative_proof_target,
                next_cumulative_weight,
                next_last_coinbase_target,
                next_last_coinbase_timestamp,
            ) = to_next_targets::<CurrentNetwork>(
                latest_cumulative_proof_target,
                combined_proof_target,
                latest_coinbase_target,
                latest_cumulative_weight,
                last_coinbase_target,
                last_coinbase_timestamp,
                next_timestamp,
            )
            .unwrap();

            // Check that missing the target threshold does the following:
            // 1. Does not reset the next_cumulative_proof_target.
            // 2. Does not update the last_coinbase_target.
            // 3. Does not update the last_coinbase_timestamp.
            assert_eq!(next_cumulative_proof_target, latest_cumulative_proof_target + combined_proof_target);
            assert_eq!(next_last_coinbase_target, last_coinbase_target);
            assert_eq!(next_last_coinbase_timestamp, last_coinbase_timestamp);

            // Check that the cumulative_weight is updated correctly.
            assert_eq!(next_cumulative_weight, latest_cumulative_weight.saturating_add(combined_proof_target));
        }
    }
}
