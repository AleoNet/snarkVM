// Copyright (C) 2019-2022 Aleo Systems Inc.
// This file is part of the snarkVM library.

// The snarkVM library is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// The snarkVM library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with the snarkVM library. If not, see <https://www.gnu.org/licenses/>.

// TODO (raychu86): Transition out of floating point arithmetic to something more precise.

// TODO (raychu86): Handle downcasting.

#[allow(unused)]
///
/// Calculate the staking reward, given the starting supply and anchor time.
///     R_staking = floor((0.025 * S) / H_Y1)
///     S = Starting supply.
///     H_Y1 = Expected block height at year 1.
///
pub(crate) fn staking_reward<const STARTING_SUPPLY: u64, const ANCHOR_TIME: i64>() -> u64 {
    // The staking percentage at genesis.
    const STAKING_PERCENTAGE: f64 = 0.025f64; // 2.5%

    let block_height_around_year_1 = estimated_block_height(ANCHOR_TIME as u64, 1);

    let reward = (STARTING_SUPPLY as f64 * STAKING_PERCENTAGE) / block_height_around_year_1 as f64;

    reward.floor() as u64
}

///
/// Calculate the coinbase reward for a given block.
///     R_coinbase = max(0, H_Y10 - H) * R_anchor * 2^((D - B) / N).
///     R_anchor = Anchor reward.
///     H_Y10 = Expected block height at year 10.
///     H = Current block height.
///     D = Time elapsed since the previous block.
///     B = Expected time per block.
///     N = Number of rounds in an epoch.
///
pub(crate) fn proving_reward<const STARTING_SUPPLY: u64, const ANCHOR_TIME: i64, const NUM_ROUNDS_PER_EPOCH: u32>(
    previous_timestamp: i64,
    timestamp: i64,
    block_height: u64,
) -> u64 {
    let block_height_around_year_10 = estimated_block_height(ANCHOR_TIME as u64, 10);

    let max = std::cmp::max(block_height_around_year_10.saturating_sub(block_height), 0);
    let anchor_reward = anchor_reward::<STARTING_SUPPLY, ANCHOR_TIME>();

    let unadjusted_reward = max * anchor_reward;

    if unadjusted_reward == 0 {
        0
    } else {
        // (max * anchor_reward) * 2^{-1 * ((timestamp - previous_timestamp) - ANCHOR_TIME) / NUM_ROUNDS_IN_EPOCH}
        retarget::<ANCHOR_TIME, NUM_ROUNDS_PER_EPOCH>(unadjusted_reward, previous_timestamp, timestamp, true)
    }
}

///
/// Calculate the anchor reward.
///     R_anchor = floor((2 * S) / (H_Y10 * (H_Y10 + 1))).
///     S = Starting supply.
///     H_Y10 = Expected block height at year 10.
///
pub(crate) fn anchor_reward<const STARTING_SUPPLY: u64, const ANCHOR_TIME: i64>() -> u64 {
    let block_height_around_year_10 = estimated_block_height(ANCHOR_TIME as u64, 10);

    let numerator = 2 * STARTING_SUPPLY;
    let denominator = block_height_around_year_10 * (block_height_around_year_10 + 1);

    (numerator as f64 / denominator as f64).floor() as u64
}

/// Returns the estimated block height after a given number of years for a specific anchor time.
pub(crate) fn estimated_block_height(anchor_time: u64, num_years: u32) -> u64 {
    const SECONDS_IN_A_YEAR: u64 = 60 * 60 * 24 * 365;

    let estimated_blocks_in_a_year = SECONDS_IN_A_YEAR / anchor_time;

    estimated_blocks_in_a_year * num_years as u64
}

/// Calculate the coinbase target for the given block height.
pub fn coinbase_target<const ANCHOR_TIME: i64, const NUM_ROUNDS_PER_EPOCH: u32>(
    previous_coinbase_target: u64,
    previous_block_timestamp: i64,
    block_timestamp: i64,
) -> u64 {
    let candidate_target = retarget::<ANCHOR_TIME, NUM_ROUNDS_PER_EPOCH>(
        previous_coinbase_target,
        previous_block_timestamp,
        block_timestamp,
        false,
    );

    core::cmp::max((2u64.pow(10)).saturating_sub(1), candidate_target)
}

/// Calculate the minimum proof target for the given coinbase target.
pub fn proof_target(coinbase_target: u64) -> u64 {
    coinbase_target.checked_shr(10).unwrap_or(0)
}

///
/// Retarget algorithm using fixed point arithmetic from https://www.reference.cash/protocol/forks/2020-11-15-asert.
///     T_{i+1} = T_i * 2^((D - B) / N).
///     T_i = Current target.
///     D = Time elapsed since the previous block.
///     B = Expected time per block.
///     N = Number of rounds in an epoch.
///
fn retarget<const ANCHOR_TIME: i64, const NUM_ROUNDS_PER_EPOCH: u32>(
    previous_target: u64,
    previous_block_timestamp: i64,
    block_timestamp: i64,
    is_inverse: bool,
) -> u64 {
    // Compute the difference in block time elapsed, defined as:
    let mut drift = {
        // Determine the block time elapsed (in seconds) since the anchor block.
        // Note: This operation includes a safety check for a repeat timestamp.
        let block_time_elapsed = core::cmp::max(block_timestamp.saturating_sub(previous_block_timestamp), 1);

        // Determine the difference in block time elapsed (in seconds).
        // Note: This operation must be *standard subtraction* to account for faster blocks.
        block_time_elapsed - ANCHOR_TIME
    };

    // If the drift is zero, return the previous target.
    if drift == 0 {
        return previous_target;
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
        let exponent = (RADIX as i128).saturating_mul(drift as i128) / NUM_ROUNDS_PER_EPOCH as i128;

        // Decompose into the integral and fractional parts.
        let integral = exponent >> RBITS;
        let fractional = (exponent - (integral << RBITS)) as u128;
        assert!(fractional < RADIX, "Ensure fractional part is within fixed point size");
        assert_eq!(exponent, integral * (RADIX as i128) + fractional as i128);

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
        match candidate_target.checked_shr((-shifts) as u32) {
            Some(target) => core::cmp::max(target, 1),
            None => 1,
        }
    } else {
        match candidate_target.checked_shl(shifts as u32) {
            Some(target) => core::cmp::max(target, 1),
            None => u64::MAX as u128,
        }
    };

    // Cap the difficulty target at `u64::MAX` if it has overflowed.
    candidate_target = core::cmp::min(candidate_target, u64::MAX as u128);

    // Cast the new target down from a u128 to a u64.
    // Ensure that the leading 64 bits are zeros.
    assert_eq!(candidate_target.checked_shr(64), Some(0));
    candidate_target as u64
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_utilities::TestRng;

    use rand::Rng;

    const NUM_GATES_PER_CREDIT: u64 = 1_000_000; // 1 million gates == 1 credit
    const STARTING_SUPPLY: u64 = 1_000_000_000 * NUM_GATES_PER_CREDIT; // 1 quadrillion gates == 1 billion credits

    const ANCHOR_TIMESTAMP: i64 = 1640179531; // 2019-01-01 00:00:00 UTC
    const ANCHOR_TIME: i64 = 15; // 15 seconds
    const NUM_ROUNDS_PER_EPOCH: u32 = 480; // The expected number of rounds per epoch (2 hours).

    const ITERATIONS: usize = 1000;

    #[test]
    fn test_anchor_reward() {
        let reward = anchor_reward::<STARTING_SUPPLY, ANCHOR_TIME>();
        assert_eq!(reward, 4);

        // Increasing the anchor time will increase the reward.
        let larger_reward = anchor_reward::<STARTING_SUPPLY, { ANCHOR_TIME + 1 }>();
        assert!(reward < larger_reward);

        // Decreasing the anchor time will decrease the reward.
        let smaller_reward = anchor_reward::<STARTING_SUPPLY, { ANCHOR_TIME - 1 }>();
        assert!(reward > smaller_reward);
    }

    #[test]
    fn test_staking_reward() {
        let reward = staking_reward::<STARTING_SUPPLY, ANCHOR_TIME>();
        assert_eq!(reward, 11_891_171);

        // Increasing the anchor time will increase the reward.
        let larger_reward = staking_reward::<STARTING_SUPPLY, { ANCHOR_TIME + 1 }>();
        assert!(reward < larger_reward);

        // Decreasing the anchor time will decrease the reward.
        let smaller_reward = staking_reward::<STARTING_SUPPLY, { ANCHOR_TIME - 1 }>();
        assert!(reward > smaller_reward);
    }

    #[test]
    fn test_proving_reward() {
        let estimated_blocks_in_10_years = estimated_block_height(ANCHOR_TIME as u64, 10);

        let mut block_height = 1;
        let mut previous_timestamp = ANCHOR_TIMESTAMP;
        let mut timestamp = ANCHOR_TIMESTAMP;

        let mut previous_reward = proving_reward::<STARTING_SUPPLY, ANCHOR_TIME, NUM_ROUNDS_PER_EPOCH>(
            previous_timestamp,
            timestamp,
            block_height,
        );

        block_height *= 2;
        timestamp = ANCHOR_TIMESTAMP + block_height as i64 * ANCHOR_TIME;

        while block_height < estimated_blocks_in_10_years {
            let reward = proving_reward::<STARTING_SUPPLY, ANCHOR_TIME, NUM_ROUNDS_PER_EPOCH>(
                previous_timestamp,
                timestamp,
                block_height,
            );
            assert!(reward <= previous_reward);

            previous_reward = reward;
            previous_timestamp = timestamp;
            block_height *= 2;
            timestamp = ANCHOR_TIMESTAMP + block_height as i64 * ANCHOR_TIME;
        }
    }

    #[test]
    fn test_proving_reward_after_10_years() {
        let estimated_blocks_in_10_years = estimated_block_height(ANCHOR_TIME as u64, 10);

        let mut block_height = estimated_blocks_in_10_years;

        for _ in 0..ITERATIONS {
            let timestamp = ANCHOR_TIMESTAMP + block_height as i64 * ANCHOR_TIME;
            let new_timestamp = timestamp + ANCHOR_TIME;

            let reward = proving_reward::<STARTING_SUPPLY, ANCHOR_TIME, NUM_ROUNDS_PER_EPOCH>(
                timestamp,
                new_timestamp,
                block_height,
            );

            assert_eq!(reward, 0);

            block_height *= 2;
        }
    }

    #[test]
    fn test_targets() {
        let mut rng = TestRng::default();

        let minimum_coinbase_target: u64 = 2u64.pow(10) - 1;

        for _ in 0..ITERATIONS {
            let previous_coinbase_target: u64 = rng.gen_range(minimum_coinbase_target..u64::MAX);
            let previous_prover_target = proof_target(previous_coinbase_target);

            let previous_timestamp = rng.gen();

            // Targets stay the same when the timestamp is as expected.
            let new_timestamp = previous_timestamp + ANCHOR_TIME;
            let new_coinbase_target = coinbase_target::<ANCHOR_TIME, NUM_ROUNDS_PER_EPOCH>(
                previous_coinbase_target,
                previous_timestamp,
                new_timestamp,
            );
            let new_prover_target = proof_target(new_coinbase_target);
            assert_eq!(new_coinbase_target, previous_coinbase_target);
            assert_eq!(new_prover_target, previous_prover_target);

            // Targets increase (easier) when the timestamp is greater than expected.
            let new_timestamp = previous_timestamp + 2 * ANCHOR_TIME;
            let new_coinbase_target = coinbase_target::<ANCHOR_TIME, NUM_ROUNDS_PER_EPOCH>(
                previous_coinbase_target,
                previous_timestamp,
                new_timestamp,
            );
            let new_prover_target = proof_target(new_coinbase_target);
            assert!(new_coinbase_target > previous_coinbase_target);
            assert!(new_prover_target > previous_prover_target);

            // Targets decrease (harder) when the timestamp is less than expected.
            let new_timestamp = previous_timestamp + ANCHOR_TIME / 2;
            let new_coinbase_target = coinbase_target::<ANCHOR_TIME, NUM_ROUNDS_PER_EPOCH>(
                previous_coinbase_target,
                previous_timestamp,
                new_timestamp,
            );
            let new_prover_target = proof_target(new_coinbase_target);

            assert!(new_coinbase_target < previous_coinbase_target);
            assert!(new_prover_target < previous_prover_target);
        }
    }
}
