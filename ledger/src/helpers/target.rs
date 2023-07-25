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

use anyhow::{anyhow, ensure, Result};

/// Calculate the staking reward, given the starting supply and anchor time.
///     R_staking = floor((0.025 * S) / H_Y1)
///     S = Starting supply.
///     H_Y1 = Anchor block height at year 1.
#[allow(dead_code)]
pub const fn staking_reward(starting_supply: u64, anchor_time: u16) -> u64 {
    // Compute the anchor block height at year 1.
    let anchor_height_at_year_1 = anchor_block_height(anchor_time, 1);
    // Compute the annual staking reward: (0.025 * S).
    let annual_staking_reward = (starting_supply / 1000) * 25;
    // Compute the staking reward: (0.025 * S) / H_Y1.
    annual_staking_reward / anchor_height_at_year_1 as u64
}

/// Calculates the coinbase reward for a given block.
///     R_coinbase = max(0, H_Y10 - H) * R_anchor * min(C_R, P) / C
///     R_anchor = Anchor reward.
///     H_Y10 = Anchor block height at year 10.
///     H = Current block height.
///     C_R = Remaining coinbase target.
///     C = Coinbase target.
///     P = Combined proof target.
pub fn coinbase_reward(
    block_height: u32,
    starting_supply: u64,
    anchor_time: u16,
    block_time: u16,
    combined_proof_target: u128,
    remaining_coinbase_target: u64,
    coinbase_target: u64,
) -> Result<u64> {
    // Ensure the remaining coinbase target is less than or equal to the coinbase target.
    ensure!(remaining_coinbase_target <= coinbase_target, "Coinbase reward portion exceeds coinbase target");

    // Compute the anchor block height at year 10.
    let anchor_height_at_year_10 = anchor_block_height(anchor_time, 10);
    // Compute the anchor reward.
    let anchor_reward = anchor_reward(starting_supply, anchor_time, block_time);
    // Compute the remaining blocks until year 10, as a u64.
    let num_remaining_blocks_to_year_10 = anchor_height_at_year_10.saturating_sub(block_height) as u64;
    // Return the coinbase reward.
    match num_remaining_blocks_to_year_10.checked_mul(anchor_reward).ok_or_else(|| anyhow!("Anchor reward overflow"))? {
        // After the anchor block height at year 10, the coinbase reward is 0.
        0 => Ok(0),
        // Until the anchor block height at year 10, the coinbase reward is determined by this equation:
        //   (num_remaining_blocks_to_year_10 * anchor_reward) * min(remaining_coinbase_target, combined_proof_target) / coinbase_target
        reward => {
            // Calculate the portion of the coinbase target to pay out. The maximum portion to pay out is the remaining coinbase target.
            let portion = core::cmp::min(remaining_coinbase_target as u128, combined_proof_target);

            // Calculate the coinbase reward.
            let reward = (reward as u128)
                .checked_mul(portion)
                .ok_or_else(|| anyhow!("Coinbase reward numerator overflow"))?
                .checked_div(coinbase_target as u128)
                .ok_or_else(|| anyhow!("Coinbase reward denominator underflow"))?;

            // Return the reward
            Ok(u64::try_from(reward)?)
        }
    }
}

/// Calculates the anchor reward.
///     R_anchor = floor((2 * S * B) / (H_Y10 * (H_Y10 + 1))).
///     S = Starting supply.
///     B = Block time.
///     H_Y10 = Expected block height at year 10.
const fn anchor_reward(starting_supply: u64, anchor_time: u16, block_time: u16) -> u64 {
    // Calculate the anchor block height at year 10.
    let anchor_height_at_year_10 = anchor_block_height(anchor_time, 10) as u64;
    // Compute the numerator.
    let numerator = 2 * starting_supply * (anchor_time / block_time) as u64;
    // Compute the denominator.
    let denominator = anchor_height_at_year_10 * (anchor_height_at_year_10 + 1);
    // Return the anchor reward.
    numerator / denominator
}

/// Returns the anchor block height after a given number of years for a specific anchor time.
pub const fn anchor_block_height(anchor_time: u16, num_years: u32) -> u32 {
    // Calculate the number of seconds in a year.
    const SECONDS_IN_A_YEAR: u32 = 60 * 60 * 24 * 365;
    // Calculate the one-year anchor block height.
    let anchor_block_height_at_year_1 = SECONDS_IN_A_YEAR / anchor_time as u32;
    // Return the anchor block height for the given number of years.
    anchor_block_height_at_year_1 * num_years
}

/// Calculate the coinbase target for the given block height.
pub fn coinbase_target(
    previous_coinbase_target: u64,
    previous_block_timestamp: i64,
    block_timestamp: i64,
    anchor_time: u16,
    num_blocks_per_epoch: u32,
    genesis_coinbase_target: u64,
) -> Result<u64> {
    // Compute the half life.
    let half_life = num_blocks_per_epoch.saturating_div(2).saturating_mul(anchor_time as u32);

    // Compute the new coinbase target.
    let candidate_target =
        retarget(previous_coinbase_target, previous_block_timestamp, block_timestamp, half_life, true, anchor_time)?;
    // Return the new coinbase target, floored at `genesis_coinbase_target`.
    Ok(core::cmp::max(genesis_coinbase_target, candidate_target))
}

/// Calculate the minimum proof target for the given coinbase target.
pub fn proof_target(coinbase_target: u64, genesis_proof_target: u64) -> u64 {
    coinbase_target.checked_shr(7).map(|target| target.saturating_add(1)).unwrap_or(genesis_proof_target)
}

/// Retarget algorithm using fixed point arithmetic from https://www.reference.cash/protocol/forks/2020-11-15-asert.
///     T_{i+1} = T_i * 2^(INV * (D - B) / TAU).
///     T_i = Current target.
///     D = Time elapsed since the previous block.
///     B = Expected time per block.
///     TAU = Rate of doubling (or half-life) in seconds.
///     INV = {-1, 1} depending on whether the target is increasing or decreasing.
fn retarget(
    previous_target: u64,
    previous_block_timestamp: i64,
    block_timestamp: i64,
    half_life: u32,
    is_inverse: bool,
    anchor_time: u16,
) -> Result<u64> {
    // Compute the difference in block time elapsed, defined as:
    let mut drift = {
        // Determine the block time elapsed (in seconds) since the previous block.
        // Note: This operation includes a safety check for a repeat timestamp.
        let block_time_elapsed = core::cmp::max(block_timestamp.saturating_sub(previous_block_timestamp), 1);

        // Determine the difference in block time elapsed (in seconds).
        // Note: This operation must be *standard subtraction* to account for faster blocks.
        block_time_elapsed - anchor_time as i64
    };

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

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::{prelude::*, Testnet3};

    type CurrentNetwork = Testnet3;

    const ITERATIONS: usize = 1000;

    const EXPECTED_ANCHOR_REWARD: u64 = 18;
    const EXPECTED_STAKING_REWARD: u64 = 29_727_929;
    const EXPECTED_COINBASE_REWARD: u64 = 227_059_182;

    #[test]
    fn test_anchor_reward() {
        let reward =
            anchor_reward(CurrentNetwork::STARTING_SUPPLY, CurrentNetwork::ANCHOR_TIME, CurrentNetwork::BLOCK_TIME);
        assert_eq!(reward, EXPECTED_ANCHOR_REWARD);

        // Increasing the anchor time will increase the reward.
        let larger_reward =
            anchor_reward(CurrentNetwork::STARTING_SUPPLY, CurrentNetwork::ANCHOR_TIME + 1, CurrentNetwork::BLOCK_TIME);
        assert!(reward < larger_reward);

        // Decreasing the anchor time will decrease the reward.
        let smaller_reward =
            anchor_reward(CurrentNetwork::STARTING_SUPPLY, CurrentNetwork::ANCHOR_TIME - 1, CurrentNetwork::BLOCK_TIME);
        assert!(reward > smaller_reward);
    }

    #[test]
    fn test_staking_reward() {
        let reward = staking_reward(CurrentNetwork::STARTING_SUPPLY, CurrentNetwork::ANCHOR_TIME);
        assert_eq!(reward, EXPECTED_STAKING_REWARD);

        // Increasing the anchor time will increase the reward.
        let larger_reward = staking_reward(CurrentNetwork::STARTING_SUPPLY, CurrentNetwork::ANCHOR_TIME + 1);
        assert!(reward < larger_reward);

        // Decreasing the anchor time will decrease the reward.
        let smaller_reward = staking_reward(CurrentNetwork::STARTING_SUPPLY, CurrentNetwork::ANCHOR_TIME - 1);
        assert!(reward > smaller_reward);
    }

    #[test]
    fn test_coinbase_reward() {
        let coinbase_target: u64 = 10000;
        let remaining_coinbase_target: u64 = coinbase_target;
        let combined_proof_target: u128 = coinbase_target as u128;

        let reward = coinbase_reward(
            1,
            CurrentNetwork::STARTING_SUPPLY,
            CurrentNetwork::ANCHOR_TIME,
            CurrentNetwork::BLOCK_TIME,
            combined_proof_target,
            remaining_coinbase_target,
            coinbase_target,
        )
        .unwrap();
        assert_eq!(reward, EXPECTED_COINBASE_REWARD);

        // Halving the combined proof target halves the reward.
        let smaller_reward = coinbase_reward(
            1,
            CurrentNetwork::STARTING_SUPPLY,
            CurrentNetwork::ANCHOR_TIME,
            CurrentNetwork::BLOCK_TIME,
            combined_proof_target / 2,
            remaining_coinbase_target,
            coinbase_target,
        )
        .unwrap();
        assert_eq!(smaller_reward, reward / 2);

        // Halving the remaining coinbase target halves the reward.
        let smaller_reward = coinbase_reward(
            1,
            CurrentNetwork::STARTING_SUPPLY,
            CurrentNetwork::ANCHOR_TIME,
            CurrentNetwork::BLOCK_TIME,
            combined_proof_target,
            remaining_coinbase_target / 2,
            coinbase_target,
        )
        .unwrap();
        assert!(reward > smaller_reward);

        // Dramatically increasing the combined proof target greater than the remaining coinbase target will not increase the reward.
        let equivalent_reward = coinbase_reward(
            1,
            CurrentNetwork::STARTING_SUPPLY,
            CurrentNetwork::ANCHOR_TIME,
            CurrentNetwork::BLOCK_TIME,
            u128::MAX,
            remaining_coinbase_target,
            coinbase_target,
        )
        .unwrap();
        assert_eq!(reward, equivalent_reward);

        // Decreasing the combined proof target to 0 will result in a reward of 0.
        let zero_reward = coinbase_reward(
            1,
            CurrentNetwork::STARTING_SUPPLY,
            CurrentNetwork::ANCHOR_TIME,
            CurrentNetwork::BLOCK_TIME,
            0,
            remaining_coinbase_target,
            coinbase_target,
        )
        .unwrap();
        assert_eq!(zero_reward, 0);
    }

    #[test]
    fn test_coinbase_reward_remaining_target() {
        let mut rng = TestRng::default();

        for _ in 0..ITERATIONS {
            // Increasing the remaining coinbase target will not increase the reward if the combined proof target is less than or equal to the remaining coinbase target.
            {
                let coinbase_target = rng.gen_range(1_000_000..1_000_000_000_000_000);
                let remaining_coinbase_target = coinbase_target / 2;
                let combined_proof_target = remaining_coinbase_target as u128 / 2;

                let reward = coinbase_reward(
                    1,
                    CurrentNetwork::STARTING_SUPPLY,
                    CurrentNetwork::ANCHOR_TIME,
                    CurrentNetwork::BLOCK_TIME,
                    combined_proof_target,
                    remaining_coinbase_target,
                    coinbase_target,
                )
                .unwrap();

                // Increasing the remaining coinbase target will not increase the reward if the combined proof target is less than or equal to the remaining coinbase target.
                let equivalent_reward = coinbase_reward(
                    1,
                    CurrentNetwork::STARTING_SUPPLY,
                    CurrentNetwork::ANCHOR_TIME,
                    CurrentNetwork::BLOCK_TIME,
                    combined_proof_target,
                    remaining_coinbase_target * 2,
                    coinbase_target,
                )
                .unwrap();
                assert_eq!(reward, equivalent_reward);

                // Decreasing the remaining coinbase will decrease the reward if the combined proof target is greater than the remaining coinbase target.
                let lower_reward = coinbase_reward(
                    1,
                    CurrentNetwork::STARTING_SUPPLY,
                    CurrentNetwork::ANCHOR_TIME,
                    CurrentNetwork::BLOCK_TIME,
                    combined_proof_target,
                    u64::try_from(combined_proof_target / 2).unwrap(),
                    coinbase_target,
                )
                .unwrap();
                assert!(reward > lower_reward);

                // Decreasing the remaining coinbase will not decrease the reward if the combined proof target is less than the remaining coinbase target.
                let equivalent_reward = coinbase_reward(
                    1,
                    CurrentNetwork::STARTING_SUPPLY,
                    CurrentNetwork::ANCHOR_TIME,
                    CurrentNetwork::BLOCK_TIME,
                    combined_proof_target,
                    rng.gen_range(u64::try_from(combined_proof_target).unwrap()..remaining_coinbase_target),
                    coinbase_target,
                )
                .unwrap();
                assert_eq!(reward, equivalent_reward);

                // Increasing the combined proof target will increase the reward if the combined proof target is less than the remaining coinbase target.
                let larger_reward = coinbase_reward(
                    1,
                    CurrentNetwork::STARTING_SUPPLY,
                    CurrentNetwork::ANCHOR_TIME,
                    CurrentNetwork::BLOCK_TIME,
                    rng.gen_range(combined_proof_target + 1..remaining_coinbase_target as u128),
                    remaining_coinbase_target,
                    coinbase_target,
                )
                .unwrap();
                assert!(larger_reward > reward);
            }
        }
    }

    #[test]
    fn test_coinbase_reward_up_to_year_10() {
        let anchor_height_at_year_10 = anchor_block_height(CurrentNetwork::ANCHOR_TIME, 10);

        let mut block_height = 1;

        let mut previous_reward = coinbase_reward(
            block_height,
            CurrentNetwork::STARTING_SUPPLY,
            CurrentNetwork::ANCHOR_TIME,
            CurrentNetwork::BLOCK_TIME,
            1,
            1,
            1,
        )
        .unwrap();

        block_height += 1;

        let mut total_reward = previous_reward;

        let coinbase_target = (CurrentNetwork::ANCHOR_TIME / CurrentNetwork::BLOCK_TIME) as u64;
        let mut index = coinbase_target;

        while block_height < anchor_height_at_year_10 {
            let reward = coinbase_reward(
                block_height,
                CurrentNetwork::STARTING_SUPPLY,
                CurrentNetwork::ANCHOR_TIME,
                CurrentNetwork::BLOCK_TIME,
                1,
                index,
                coinbase_target,
            )
            .unwrap();
            assert!(reward <= previous_reward);

            total_reward += reward;
            previous_reward = reward;
            block_height += 1;

            // Update the index.
            index = match index.saturating_sub(1) {
                0 => coinbase_target,
                index => index,
            };
        }

        println!("Total reward up to year 10: {}", total_reward);
    }

    #[test]
    fn test_coinbase_reward_after_year_10() {
        let mut rng = TestRng::default();

        let anchor_height_at_year_10 = anchor_block_height(CurrentNetwork::ANCHOR_TIME, 10);

        // Check that block `anchor_height_at_year_10` has a reward of 0.
        let reward = coinbase_reward(
            anchor_height_at_year_10,
            CurrentNetwork::STARTING_SUPPLY,
            CurrentNetwork::ANCHOR_TIME,
            CurrentNetwork::BLOCK_TIME,
            1,
            1,
            1,
        )
        .unwrap();
        assert_eq!(reward, 0);

        // Check that the subsequent blocks have a reward of 0.
        for _ in 0..ITERATIONS {
            let block_height: u32 = rng.gen_range(anchor_height_at_year_10..anchor_height_at_year_10 * 10);
            let coinbase_target = rng.gen_range(1_000_000..1_000_000_000_000_000);
            let remaining_coinbase_target = rng.gen_range(0..coinbase_target);
            let combined_proof_target = rng.gen_range(0..coinbase_target as u128);

            let reward = coinbase_reward(
                block_height,
                CurrentNetwork::STARTING_SUPPLY,
                CurrentNetwork::ANCHOR_TIME,
                CurrentNetwork::BLOCK_TIME,
                combined_proof_target,
                remaining_coinbase_target,
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
            let previous_prover_target = proof_target(previous_coinbase_target, CurrentNetwork::GENESIS_PROOF_TARGET);

            let previous_timestamp = rng.gen();

            // Targets stay the same when the timestamp is as expected.
            let new_timestamp = previous_timestamp + CurrentNetwork::ANCHOR_TIME as i64;
            let new_coinbase_target = coinbase_target(
                previous_coinbase_target,
                previous_timestamp,
                new_timestamp,
                CurrentNetwork::ANCHOR_TIME,
                CurrentNetwork::NUM_BLOCKS_PER_EPOCH,
                CurrentNetwork::GENESIS_COINBASE_TARGET,
            )
            .unwrap();
            let new_prover_target = proof_target(new_coinbase_target, CurrentNetwork::GENESIS_PROOF_TARGET);
            assert_eq!(new_coinbase_target, previous_coinbase_target);
            assert_eq!(new_prover_target, previous_prover_target);

            // Targets decrease (easier) when the timestamp is greater than expected.
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
            let new_prover_target = proof_target(new_coinbase_target, CurrentNetwork::GENESIS_PROOF_TARGET);
            assert!(new_coinbase_target < previous_coinbase_target);
            assert!(new_prover_target < previous_prover_target);

            // Targets increase (harder) when the timestamp is less than expected.
            let new_timestamp = previous_timestamp + CurrentNetwork::ANCHOR_TIME as i64 / 2;
            let new_coinbase_target = coinbase_target(
                previous_coinbase_target,
                previous_timestamp,
                new_timestamp,
                CurrentNetwork::ANCHOR_TIME,
                CurrentNetwork::NUM_BLOCKS_PER_EPOCH,
                CurrentNetwork::GENESIS_COINBASE_TARGET,
            )
            .unwrap();
            let new_prover_target = proof_target(new_coinbase_target, CurrentNetwork::GENESIS_PROOF_TARGET);

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

            // New coinbase target is greater than half if the elapsed time equals the half life.
            let new_timestamp = previous_timestamp + half_life;
            let new_coinbase_target = coinbase_target(
                previous_coinbase_target,
                previous_timestamp,
                new_timestamp,
                CurrentNetwork::ANCHOR_TIME,
                CurrentNetwork::NUM_BLOCKS_PER_EPOCH,
                CurrentNetwork::GENESIS_COINBASE_TARGET,
            )
            .unwrap();

            assert!(new_coinbase_target > previous_coinbase_target / 2);

            // New coinbase target is halved if the elapsed time is 1 anchor time past the half life.
            let new_timestamp = previous_timestamp + half_life + CurrentNetwork::ANCHOR_TIME as i64;
            let new_coinbase_target = coinbase_target(
                previous_coinbase_target,
                previous_timestamp,
                new_timestamp,
                CurrentNetwork::ANCHOR_TIME,
                CurrentNetwork::NUM_BLOCKS_PER_EPOCH,
                CurrentNetwork::GENESIS_COINBASE_TARGET,
            )
            .unwrap();

            assert_eq!(new_coinbase_target, previous_coinbase_target / 2);

            // New coinbase target is less than half if the elapsed time is more than 1 anchor time past the half life.
            let new_timestamp = previous_timestamp + half_life + 2 * CurrentNetwork::ANCHOR_TIME as i64;
            let new_coinbase_target = coinbase_target(
                previous_coinbase_target,
                previous_timestamp,
                new_timestamp,
                CurrentNetwork::ANCHOR_TIME,
                CurrentNetwork::NUM_BLOCKS_PER_EPOCH,
                CurrentNetwork::GENESIS_COINBASE_TARGET,
            )
            .unwrap();

            assert!(new_coinbase_target < previous_coinbase_target / 2);
        }
    }

    #[test]
    fn test_target_doubling() {
        let mut rng = TestRng::default();

        // The custom block time that is faster than the anchor time.
        const BLOCK_TIME: u32 = 15;
        // The expected number of blocks before the coinbase target is doubled.
        const EXPECTED_NUM_BLOCKS_TO_DOUBLE: u32 = 321;

        let minimum_coinbase_target: u64 = 2u64.pow(10) - 1;

        let initial_coinbase_target: u64 = rng.gen_range(minimum_coinbase_target..u64::MAX / 2);
        let initial_timestamp: i64 = rng.gen();
        let mut previous_coinbase_target: u64 = initial_coinbase_target;
        let mut previous_timestamp = initial_timestamp;
        let mut num_blocks = 0;

        while previous_coinbase_target < initial_coinbase_target * 2 {
            // Targets increase (harder) when the timestamp is less than expected.
            let new_timestamp = previous_timestamp + BLOCK_TIME as i64;
            let new_coinbase_target = coinbase_target(
                previous_coinbase_target,
                previous_timestamp,
                new_timestamp,
                CurrentNetwork::ANCHOR_TIME,
                CurrentNetwork::NUM_BLOCKS_PER_EPOCH,
                CurrentNetwork::GENESIS_COINBASE_TARGET,
            )
            .unwrap();

            assert!(new_coinbase_target > previous_coinbase_target);

            previous_coinbase_target = new_coinbase_target;
            previous_timestamp = new_timestamp;
            num_blocks += 1;
        }

        println!(
            "For block times of {}s and anchor time of {}s, doubling the coinbase target took {num_blocks} blocks. ({} seconds)",
            BLOCK_TIME,
            CurrentNetwork::NUM_BLOCKS_PER_EPOCH,
            previous_timestamp - initial_timestamp
        );

        assert_eq!(EXPECTED_NUM_BLOCKS_TO_DOUBLE, num_blocks);
    }
}
