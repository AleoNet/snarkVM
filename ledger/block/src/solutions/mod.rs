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

use console::network::prelude::*;
use ledger_coinbase::CoinbaseSolution;
use ledger_committee::Committee;
use ledger_narwhal_batch_header::BatchHeader;

#[derive(Clone, Eq, PartialEq)]
pub struct Solutions<N: Network> {
    /// The prover solutions for the coinbase puzzle.
    solutions: Option<CoinbaseSolution<N>>,
}

impl<N: Network> Solutions<N> {
    /// The maximum number of aborted solutions allowed in a block.
    pub const MAX_ABORTED_SOLUTIONS: usize = BatchHeader::<N>::MAX_TRANSMISSIONS_PER_BATCH
        * BatchHeader::<N>::MAX_GC_ROUNDS
        * Committee::<N>::MAX_COMMITTEE_SIZE as usize;
}

impl<N: Network> Solutions<N> {
    /// Initializes a new instance of the solutions.
    pub fn new(solutions: CoinbaseSolution<N>) -> Result<Self> {
        // Return the solutions.
        Ok(Self { solutions: Some(solutions) })
    }
}
