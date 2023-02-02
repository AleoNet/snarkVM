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

impl<N: Network> FromStr for ProverSolution<N> {
    type Err = Error;

    /// Initializes the prover solution from a JSON-string.
    fn from_str(partial_prover_solution: &str) -> Result<Self, Self::Err> {
        Ok(serde_json::from_str(partial_prover_solution)?)
    }
}

impl<N: Network> Debug for ProverSolution<N> {
    /// Prints the prover solution as a JSON-string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for ProverSolution<N> {
    /// Displays the prover solution as a JSON-string.
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
        let private_key = PrivateKey::<CurrentNetwork>::new(&mut rng)?;
        let address = Address::try_from(private_key)?;

        // Sample a new prover puzzle solution.
        let partial_solution = PartialSolution::new(address, u64::rand(&mut rng), KZGCommitment(rng.gen()));
        let expected = ProverSolution::new(partial_solution, KZGProof { w: rng.gen(), random_v: None });

        // Check the string representation.
        let candidate = expected.to_string();
        assert_eq!(expected, ProverSolution::from_str(&candidate)?);

        Ok(())
    }
}
