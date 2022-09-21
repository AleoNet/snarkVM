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

pub struct BlockRewards;

impl BlockRewards {
    /// Calculate the anchor reward.
    pub fn anchor_reward<const STARTING_SUPPLY: u64, const ANCHOR_TIME: u64>() -> u64 {
        let block_height_around_year_10 = Self::estimated_block_height(ANCHOR_TIME, 10);

        let numerator = 2 * STARTING_SUPPLY;
        let denominator = block_height_around_year_10 * (block_height_around_year_10 + 1);

        (numerator as f64 / denominator as f64).floor() as u64
    }

    /// Calculate the staking reward, given the starting supply and anchor time.
    pub fn staking_reward<const STARTING_SUPPLY: u64, const ANCHOR_TIME: u64>() -> u64 {
        // The staking percentage at genesis.
        const STAKING_PERCENTAGE: f64 = 0.025f64; // 2.5%

        let block_height_around_year_1 = Self::estimated_block_height(ANCHOR_TIME, 1);

        let reward = (STARTING_SUPPLY as f64 * STAKING_PERCENTAGE) / block_height_around_year_1 as f64;

        reward.floor() as u64
    }

    /// Calculate the coinbase reward for a given block.
    pub fn coinbase_reward<const STARTING_SUPPLY: u64, const ANCHOR_TIMESTAMP: u64, const ANCHOR_TIME: u64>(
        num_validators: u64,
        timestamp: u64,
        block_height: u64,
    ) -> f64 {
        let block_height_around_year_10 = Self::estimated_block_height(ANCHOR_TIME, 10);

        let max = std::cmp::max(block_height_around_year_10.saturating_sub(block_height), 0);
        let anchor_reward = Self::anchor_reward::<STARTING_SUPPLY, ANCHOR_TIME>();
        let factor = Self::factor::<ANCHOR_TIMESTAMP, ANCHOR_TIME>(num_validators, timestamp, block_height);

        (max * anchor_reward) as f64 * 2f64.powf(-1f64 * factor)
    }

    /// Calculate the coinbase target for the given block height.
    fn coinbase_target<const ANCHOR_TIMESTAMP: u64, const ANCHOR_TIME: u64>(
        previous_coinbase_target: u64,
        num_validators: u64,
        timestamp: u64,
        block_height: u64,
    ) -> u64 {
        let factor = Self::factor::<ANCHOR_TIMESTAMP, ANCHOR_TIME>(num_validators, timestamp, block_height);

        // TODO (raychu86): Check precision.

        match factor {
            0.0 => previous_coinbase_target,
            _ => ((previous_coinbase_target as f64) * 2f64.powf(-1f64 * factor)) as u64,
        }
    }

    /// Calculate the minimum prover target for the given block height.
    fn prover_target<const ANCHOR_TIMESTAMP: u64, const ANCHOR_TIME: u64>(
        previous_prover_target: u64,
        num_validators: u64,
        timestamp: u64,
        block_height: u64,
    ) -> u64 {
        let factor = Self::factor::<ANCHOR_TIMESTAMP, ANCHOR_TIME>(num_validators, timestamp, block_height);

        // TODO (raychu86): Check precision.

        match factor {
            0.0 => previous_prover_target,
            _ => ((previous_prover_target as f64) * 2f64.powf(-1f64 * factor)) as u64,
        }
    }

    /// Calculate the factor used in the target adjustment algorithm and coinbase reward.
    fn factor<const ANCHOR_TIMESTAMP: u64, const ANCHOR_TIME: u64>(
        num_validators: u64,
        timestamp: u64,
        block_height: u64,
    ) -> f64 {
        let numerator: f64 = (timestamp as f64 - ANCHOR_TIMESTAMP as f64) - (block_height as f64 * ANCHOR_TIME as f64);
        let denominator = num_validators * ANCHOR_TIME;

        numerator as f64 / denominator as f64
    }

    /// Returns the estimated block height after a given number of years for a specific anchor time.
    fn estimated_block_height(anchor_time: u64, num_years: u32) -> u64 {
        const SECONDS_IN_A_YEAR: u64 = 60 * 60 * 24 * 365;

        let estimated_blocks_in_a_year = SECONDS_IN_A_YEAR / anchor_time;

        estimated_blocks_in_a_year * num_years as u64
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_utilities::TestRng;

    use rand::Rng;

    const NUM_GATES_PER_CREDIT: u64 = 1_000_000; // 1 million gates == 1 credit
    const STARTING_SUPPLY: u64 = 1_000_000_000 * NUM_GATES_PER_CREDIT; // 1 quadrillion gates == 1 billion credits

    const ANCHOR_TIMESTAMP: u64 = 1640179531; // 2019-01-01 00:00:00 UTC
    const ANCHOR_TIME: u64 = 15; // 15 seconds

    #[test]
    fn test_anchor_reward() {
        let reward = BlockRewards::anchor_reward::<STARTING_SUPPLY, ANCHOR_TIME>();
        assert_eq!(reward, 4);

        // Increasing the anchor time will increase the reward.
        let larger_reward = BlockRewards::anchor_reward::<STARTING_SUPPLY, { ANCHOR_TIME + 1 }>();
        assert!(reward < larger_reward);

        // Decreasing the anchor time will decrease the reward.
        let smaller_reward = BlockRewards::anchor_reward::<STARTING_SUPPLY, { ANCHOR_TIME - 1 }>();
        assert!(reward > smaller_reward);
    }

    #[test]
    fn test_staking_reward() {
        let reward = BlockRewards::staking_reward::<STARTING_SUPPLY, ANCHOR_TIME>();
        assert_eq!(reward, 11_891_171);

        // Increasing the anchor time will increase the reward.
        let larger_reward = BlockRewards::staking_reward::<STARTING_SUPPLY, { ANCHOR_TIME + 1 }>();
        assert!(reward < larger_reward);

        // Decreasing the anchor time will decrease the reward.
        let smaller_reward = BlockRewards::staking_reward::<STARTING_SUPPLY, { ANCHOR_TIME - 1 }>();
        assert!(reward > smaller_reward);
    }

    #[test]
    fn test_coinbase_reward() {
        let estimated_blocks_in_10_years = BlockRewards::estimated_block_height(ANCHOR_TIME, 10);

        let mut block_height = 1;
        let mut timestamp = ANCHOR_TIMESTAMP;

        let mut previous_reward = BlockRewards::coinbase_reward::<STARTING_SUPPLY, ANCHOR_TIMESTAMP, ANCHOR_TIME>(
            NUM_GATES_PER_CREDIT,
            timestamp,
            block_height,
        );

        block_height *= 2;
        timestamp = ANCHOR_TIMESTAMP + block_height * ANCHOR_TIME;

        while block_height < estimated_blocks_in_10_years {
            let reward = BlockRewards::coinbase_reward::<STARTING_SUPPLY, ANCHOR_TIMESTAMP, ANCHOR_TIME>(
                NUM_GATES_PER_CREDIT,
                timestamp,
                block_height,
            );
            assert!(reward <= previous_reward);

            previous_reward = reward;
            block_height *= 2;
            timestamp = ANCHOR_TIMESTAMP + block_height * ANCHOR_TIME;
        }
    }

    #[test]
    fn test_coinbase_reward_after_10_years() {
        let estimated_blocks_in_10_years = BlockRewards::estimated_block_height(ANCHOR_TIME, 10);

        let mut block_height = estimated_blocks_in_10_years;

        for _ in 0..10 {
            let timestamp = ANCHOR_TIMESTAMP + block_height * ANCHOR_TIME;

            let reward = BlockRewards::coinbase_reward::<STARTING_SUPPLY, ANCHOR_TIMESTAMP, ANCHOR_TIME>(
                NUM_GATES_PER_CREDIT,
                timestamp,
                block_height,
            );

            assert_eq!(reward, 0.0);

            block_height *= 2;
        }
    }

    #[test]
    fn test_factor() {
        let num_validators = 100;
        let mut block_height = 1;

        for _ in 0..10 {
            // Factor is 0 when the timestamp is as expected for a given block height.
            let timestamp = ANCHOR_TIMESTAMP + block_height * ANCHOR_TIME;
            let f = BlockRewards::factor::<ANCHOR_TIMESTAMP, ANCHOR_TIME>(num_validators, timestamp, block_height);
            assert_eq!(f, 0.0);

            // Factor greater than 0 when the timestamp is greater than expected for a given block height.
            let timestamp = ANCHOR_TIMESTAMP + (block_height + 1) * ANCHOR_TIME;
            let f = BlockRewards::factor::<ANCHOR_TIMESTAMP, ANCHOR_TIME>(num_validators, timestamp, block_height);
            assert!(f > 0.0);

            // Factor less than 0 when the timestamp is less than expected for a given block height.
            let timestamp = ANCHOR_TIMESTAMP + (block_height - 1) * ANCHOR_TIME;
            let f = BlockRewards::factor::<ANCHOR_TIMESTAMP, ANCHOR_TIME>(num_validators, timestamp, block_height);
            assert!(f < 0.0);

            block_height *= 2;
        }
    }

    #[test]
    fn test_targets() {
        let num_validators = 20;
        let mut block_height = 1;

        let mut rng = TestRng::default();

        let previous_coinbase_target: u64 = rng.gen();
        let previous_prover_target = previous_coinbase_target / 100;

        for _ in 0..10 {
            // Targets stay the same when the timestamp is as expected for a given block height.
            let timestamp = ANCHOR_TIMESTAMP + block_height * ANCHOR_TIME;
            let coinbase_target = BlockRewards::coinbase_target::<ANCHOR_TIMESTAMP, ANCHOR_TIME>(
                previous_coinbase_target,
                num_validators,
                timestamp,
                block_height,
            );
            let prover_target = BlockRewards::prover_target::<ANCHOR_TIMESTAMP, ANCHOR_TIME>(
                previous_prover_target,
                num_validators,
                timestamp,
                block_height,
            );
            assert_eq!(coinbase_target, previous_coinbase_target);
            assert_eq!(prover_target, previous_prover_target);

            // Targets decrease when the timestamp is greater than expected for a given block height.
            let timestamp = ANCHOR_TIMESTAMP + (block_height + 1) * ANCHOR_TIME;
            let coinbase_target = BlockRewards::coinbase_target::<ANCHOR_TIMESTAMP, ANCHOR_TIME>(
                previous_coinbase_target,
                num_validators,
                timestamp,
                block_height,
            );
            let prover_target = BlockRewards::prover_target::<ANCHOR_TIMESTAMP, ANCHOR_TIME>(
                previous_prover_target,
                num_validators,
                timestamp,
                block_height,
            );
            assert!(coinbase_target < previous_coinbase_target);
            assert!(prover_target < previous_prover_target);

            // Targets increase when the timestamp is less than expected for a given block height.
            let timestamp = ANCHOR_TIMESTAMP + (block_height - 1) * ANCHOR_TIME;
            let coinbase_target = BlockRewards::coinbase_target::<ANCHOR_TIMESTAMP, ANCHOR_TIME>(
                previous_coinbase_target,
                num_validators,
                timestamp,
                block_height,
            );
            let prover_target = BlockRewards::prover_target::<ANCHOR_TIMESTAMP, ANCHOR_TIME>(
                previous_prover_target,
                num_validators,
                timestamp,
                block_height,
            );
            assert!(coinbase_target > previous_coinbase_target);
            assert!(prover_target > previous_prover_target);

            block_height += 1;
        }
    }
}
