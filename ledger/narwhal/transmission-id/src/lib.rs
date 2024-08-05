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

#![forbid(unsafe_code)]
#![warn(clippy::cast_possible_truncation)]

mod bytes;
mod serialize;
mod string;

use console::{network::TRANSACTION_PREFIX, prelude::*};
use ledger_puzzle::{SolutionID, SOLUTION_ID_PREFIX};

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum TransmissionID<N: Network> {
    /// A ratification.
    Ratification,
    /// A solution.
    Solution(SolutionID<N>, N::TransmissionChecksum),
    /// A transaction.
    Transaction(N::TransactionID, N::TransmissionChecksum),
}

impl<N: Network> From<(SolutionID<N>, N::TransmissionChecksum)> for TransmissionID<N> {
    /// Converts the solution ID and checksum into a transmission ID.
    fn from((solution_id, checksum): (SolutionID<N>, N::TransmissionChecksum)) -> Self {
        Self::Solution(solution_id, checksum)
    }
}

impl<N: Network> From<(&N::TransactionID, &N::TransmissionChecksum)> for TransmissionID<N> {
    /// Converts the transaction ID and checksum into a transmission ID.
    fn from((transaction_id, checksum): (&N::TransactionID, &N::TransmissionChecksum)) -> Self {
        Self::Transaction(*transaction_id, *checksum)
    }
}

impl<N: Network> TransmissionID<N> {
    /// Returns the solution ID if the transmission is a solution.
    pub fn solution(&self) -> Option<SolutionID<N>> {
        match self {
            Self::Solution(solution_id, _) => Some(*solution_id),
            _ => None,
        }
    }

    /// Returns the transaction ID if the transmission is a transaction.
    pub fn transaction(&self) -> Option<N::TransactionID> {
        match self {
            Self::Transaction(transaction_id, _) => Some(*transaction_id),
            _ => None,
        }
    }

    /// Returns the checksum if the transmission is a solution or a transaction.
    pub fn checksum(&self) -> Option<N::TransmissionChecksum> {
        match self {
            Self::Ratification => None,
            Self::Solution(_, checksum) => Some(*checksum),
            Self::Transaction(_, checksum) => Some(*checksum),
        }
    }
}

#[cfg(any(test, feature = "test-helpers"))]
pub mod test_helpers {
    use super::*;
    use console::{
        network::MainnetV0,
        prelude::{Rng, TestRng, Uniform},
        types::Field,
    };

    type CurrentNetwork = MainnetV0;

    /// Returns a list of sample transmission IDs, sampled at random.
    pub fn sample_transmission_ids(rng: &mut TestRng) -> Vec<TransmissionID<CurrentNetwork>> {
        // Initialize a sample vector.
        let mut sample = Vec::with_capacity(10);
        // Append sample solution IDs.
        for _ in 0..5 {
            sample.push(TransmissionID::Solution(
                SolutionID::from(rng.gen::<u64>()),
                <CurrentNetwork as Network>::TransmissionChecksum::from(rng.gen::<u128>()),
            ));
        }
        // Append sample transaction IDs.
        for _ in 0..5 {
            let id = TransmissionID::Transaction(
                <CurrentNetwork as Network>::TransactionID::from(Field::rand(rng)),
                <CurrentNetwork as Network>::TransmissionChecksum::from(rng.gen::<u128>()),
            );
            sample.push(id);
        }
        // Return the sample vector.
        sample
    }
}
