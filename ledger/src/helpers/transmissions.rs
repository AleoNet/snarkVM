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

use console::network::Network;
use ledger_block::{Ratify, Transaction};
use ledger_coinbase::ProverSolution;
use ledger_narwhal::Transmission;

use anyhow::Result;

/// Takes in an iterator of transmissions and returns a tuple of ratifications, solutions, and transactions.
pub fn decouple_transmissions<N: Network>(
    transmissions: impl Iterator<Item = Transmission<N>>,
) -> Result<(Vec<Ratify<N>>, Vec<ProverSolution<N>>, Vec<Transaction<N>>)> {
    // Initialize a list for the ratifications.
    let mut ratifications = Vec::new();
    // Initialize a list for the solutions.
    let mut solutions = Vec::new();
    // Initialize a list for the transactions.
    let mut transactions = Vec::new();

    // Iterate over the transmissions.
    for transmission in transmissions {
        match transmission {
            Transmission::Ratification => (), // ratifications.push();
            Transmission::Solution(solution) => solutions.push(solution.deserialize_blocking()?),
            Transmission::Transaction(transaction) => transactions.push(transaction.deserialize_blocking()?),
        }
    }
    // Return the ratifications, solutions, and transactions.
    Ok((ratifications, solutions, transactions))
}
