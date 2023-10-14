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
use ledger_committee::Committee;

use indexmap::IndexMap;

type Variant = u8;
/// A helper type to represent the public balances.
type PublicBalances<N> = IndexMap<Address<N>, u64>;

#[derive(Clone, PartialEq, Eq)]
pub enum Ratify<N: Network> {
    /// The genesis.
    Genesis(Committee<N>, PublicBalances<N>),
    /// The block reward.
    BlockReward(u64),
    /// The puzzle reward.
    PuzzleReward(u64),
}

impl<N: Network> Ratify<N> {
    /// Returns the ratification ID.
    pub fn to_id(&self) -> Result<N::RatificationID> {
        Ok(N::hash_bhp1024(&self.to_bytes_le()?.to_bits_le())?.into())
    }
}

#[cfg(test)]
pub(crate) mod test_helpers {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    pub(crate) fn sample_ratifications(rng: &mut TestRng) -> Vec<Ratify<CurrentNetwork>> {
        let committee = ledger_committee::test_helpers::sample_committee(rng);
        let mut public_balances = PublicBalances::new();
        for (address, _) in committee.members().iter() {
            public_balances.insert(*address, rng.gen());
        }

        vec![
            Ratify::Genesis(committee, public_balances),
            Ratify::BlockReward(rng.gen()),
            Ratify::PuzzleReward(rng.gen()),
        ]
    }
}
