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

use crate::{CoinbaseSolution, Ratify, Transactions};
use console::network::prelude::*;

/// The confirmed transmissions included in the block.
#[derive(Clone, PartialEq, Eq)]
pub struct ConfirmedTransmissions<N: Network> {
    /// The transactions in this block.
    transactions: Transactions<N>,
    /// The ratifications in this block.
    ratifications: Vec<Ratify<N>>,
    /// The coinbase solution.
    coinbase: Option<CoinbaseSolution<N>>,
}

impl<N: Network> ConfirmedTransmissions<N> {
    /// Initializes a new instance of  `ConfirmedTransmissions`.
    pub fn from(
        transactions: Transactions<N>,
        ratifications: Vec<Ratify<N>>,
        coinbase: Option<CoinbaseSolution<N>>,
    ) -> Self {
        Self { transactions, ratifications, coinbase }
    }

    /// Returns the transactions.
    pub fn transactions(&self) -> &Transactions<N> {
        &self.transactions
    }

    /// Returns the ratifications.
    pub const fn ratifications(&self) -> &Vec<Ratify<N>> {
        &self.ratifications
    }

    /// Returns the coinbase solution.
    pub const fn coinbase(&self) -> Option<&CoinbaseSolution<N>> {
        self.coinbase.as_ref()
    }
}

#[cfg(test)]
pub mod test_helpers {
    use super::*;

    type CurrentNetwork = console::network::Testnet3;

    /// Samples a block confirmed transmissions.
    pub(crate) fn sample_confirmed_transmissions(rng: &mut TestRng) -> ConfirmedTransmissions<CurrentNetwork> {
        // Sample the transactions.
        let transactions = crate::transactions::test_helpers::sample_block_transactions(rng);

        // Sample the ratifications.
        let ratify = crate::ratify::test_helpers::sample_ratify_objects(rng);

        // Sample the coinbase.
        let coinbase = crate::test_helpers::sample_genesis_block(rng).coinbase;

        ConfirmedTransmissions::from(transactions, ratify, coinbase)
    }
}
