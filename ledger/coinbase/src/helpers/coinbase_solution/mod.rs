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

use super::*;

/// The coinbase puzzle solution constructed by accumulating the individual prover solutions.
#[derive(Clone, Eq, PartialEq, Hash)]
pub struct CoinbaseSolution<N: Network> {
    /// The partial solutions of the coinbase puzzle, which are aggregated into a single solution.
    partial_solutions: Vec<PartialSolution<N>>,
    /// The KZG proof of the coinbase solution.
    proof: PuzzleProof<N>,
}

impl<N: Network> CoinbaseSolution<N> {
    /// Initializes a new instance of a coinbase solution.
    pub const fn new(partial_solutions: Vec<PartialSolution<N>>, proof: PuzzleProof<N>) -> Self {
        Self { partial_solutions, proof }
    }

    /// Returns the partial solutions.
    pub fn partial_solutions(&self) -> &[PartialSolution<N>] {
        &self.partial_solutions
    }

    /// Returns the puzzle commitments.
    pub fn puzzle_commitments(&self) -> impl '_ + Iterator<Item = PuzzleCommitment<N>> {
        self.partial_solutions.iter().map(|s| s.commitment())
    }

    /// Returns the KZG proof.
    pub const fn proof(&self) -> &PuzzleProof<N> {
        &self.proof
    }

    /// Returns the number of partial solutions.
    pub fn len(&self) -> usize {
        self.partial_solutions.len()
    }

    /// Returns `true` if there are no partial solutions.
    pub fn is_empty(&self) -> bool {
        self.partial_solutions.is_empty()
    }

    /// Returns the cumulative sum of the prover solutions.
    pub fn to_cumulative_proof_target(&self) -> Result<u128> {
        // Compute the cumulative target as a u128.
        self.partial_solutions.iter().try_fold(0u128, |cumulative, solution| {
            cumulative.checked_add(solution.to_target()? as u128).ok_or_else(|| anyhow!("Cumulative target overflowed"))
        })
    }

    /// Returns the accumulator challenge point.
    pub fn to_accumulator_point(&self) -> Result<Field<N>> {
        let mut challenge_points =
            hash_commitments(self.partial_solutions.iter().map(|solution| *solution.commitment()))?;
        ensure!(challenge_points.len() == self.partial_solutions.len() + 1, "Invalid number of challenge points");

        // Pop the last challenge point as the accumulator challenge point.
        match challenge_points.pop() {
            Some(point) => Ok(Field::new(point)),
            None => bail!("Missing the accumulator challenge point"),
        }
    }
}
