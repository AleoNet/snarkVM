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

use indexmap::IndexMap;

/// The coinbase puzzle solution is composed of individual prover solutions.
#[derive(Clone, Eq, PartialEq)]
pub struct CoinbaseSolution<N: Network> {
    /// The prover solutions for the coinbase puzzle.
    solutions: IndexMap<PuzzleCommitment<N>, ProverSolution<N>>,
}

impl<N: Network> CoinbaseSolution<N> {
    /// Initializes a new instance of the solutions.
    pub fn new(solutions: Vec<ProverSolution<N>>) -> Self {
        Self { solutions: solutions.into_iter().map(|solution| (solution.commitment(), solution)).collect() }
    }

    /// Returns the puzzle commitments.
    pub fn puzzle_commitments(&self) -> impl '_ + Iterator<Item = &PuzzleCommitment<N>> {
        self.solutions.keys()
    }

    /// Returns the number of solutions.
    pub fn len(&self) -> usize {
        self.solutions.len()
    }

    /// Returns `true` if there are no solutions.
    pub fn is_empty(&self) -> bool {
        self.solutions.is_empty()
    }

    /// Returns the prover solution for the puzzle commitment.
    pub fn get_solution(&self, puzzle_commitment: &PuzzleCommitment<N>) -> Option<&ProverSolution<N>> {
        self.solutions.get(puzzle_commitment)
    }

    /// Returns the combined sum of the prover solutions.
    pub fn to_combined_proof_target(&self) -> Result<u128> {
        // Compute the combined proof target as a u128.
        self.solutions.values().try_fold(0u128, |combined, solution| {
            combined.checked_add(solution.to_target()? as u128).ok_or_else(|| anyhow!("Combined target overflowed"))
        })
    }

    /// Returns the accumulator challenge point.
    pub fn to_accumulator_point(&self) -> Result<Field<N>> {
        let mut challenge_points = hash_commitments(self.solutions.keys().map(|pcm| **pcm))?;
        ensure!(challenge_points.len() == self.solutions.len() + 1, "Invalid number of challenge points");

        // Pop the last challenge point as the accumulator challenge point.
        match challenge_points.pop() {
            Some(point) => Ok(Field::new(point)),
            None => bail!("Missing the accumulator challenge point"),
        }
    }
}

impl<N: Network> Deref for CoinbaseSolution<N> {
    type Target = IndexMap<PuzzleCommitment<N>, ProverSolution<N>>;

    fn deref(&self) -> &Self::Target {
        &self.solutions
    }
}
