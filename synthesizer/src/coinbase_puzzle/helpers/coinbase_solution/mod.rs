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
