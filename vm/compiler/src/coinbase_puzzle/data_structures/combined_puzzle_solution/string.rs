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

use super::*;

impl<N: Network> FromStr for CombinedPuzzleSolution<N> {
    type Err = Error;

    /// Initializes the block from a JSON-string.
    fn from_str(combined_puzzle_solution: &str) -> Result<Self, Self::Err> {
        Ok(serde_json::from_str(combined_puzzle_solution)?)
    }
}

impl<N: Network> Debug for CombinedPuzzleSolution<N> {
    /// Prints the CombinedPuzzleSolution as a JSON-string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for CombinedPuzzleSolution<N> {
    /// Displays the CombinedPuzzleSolution as a JSON-string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", serde_json::to_string(self).map_err::<fmt::Error, _>(ser::Error::custom)?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::{account::PrivateKey, network::Testnet3};

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_string() -> Result<()> {
        let mut rng = TestRng::default();

        // Sample a new combined puzzle solution.
        let mut individual_puzzle_solutions = vec![];
        for _ in 0..rng.gen_range(1..10) {
            let private_key = PrivateKey::<CurrentNetwork>::new(&mut rng)?;
            let address = Address::try_from(private_key)?;

            individual_puzzle_solutions.push(PartialProverSolution::new(
                address,
                u64::rand(&mut rng),
                Commitment(rng.gen()),
            ));
        }
        let expected = CombinedPuzzleSolution::new(individual_puzzle_solutions, Proof { w: rng.gen(), random_v: None });

        // Check the string representation.
        let candidate = format!("{expected}");
        assert_eq!(expected, CombinedPuzzleSolution::from_str(&candidate)?);

        Ok(())
    }
}
