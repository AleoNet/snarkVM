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

mod bytes;
mod serialize;
mod string;

use console::{network::prelude::*, types::Address};

type Variant = u8;

#[derive(Copy, Clone, PartialEq, Eq)]
pub enum Ratify<N: Network> {
    /// The proving reward.
    ProvingReward(Address<N>, u64),
    /// The staking reward.
    StakingReward(Address<N>, u64),
}

#[cfg(any(test, feature = "test"))]
mod test_helpers {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    pub(crate) fn sample_ratify_objects(rng: &mut TestRng) -> Vec<Ratify<CurrentNetwork>> {
        vec![Ratify::ProvingReward(Address::new(rng.gen()), 100), Ratify::StakingReward(Address::new(rng.gen()), 200)]
    }
}
