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

use super::*;

impl<N: Network> FromStr for PartialSolution<N> {
    type Err = Error;

    /// Initializes the partial solution from a JSON-string.
    fn from_str(partial_prover_solution: &str) -> Result<Self, Self::Err> {
        Ok(serde_json::from_str(partial_prover_solution)?)
    }
}

impl<N: Network> Debug for PartialSolution<N> {
    /// Prints the partial solution as a JSON-string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for PartialSolution<N> {
    /// Displays the partial solution as a JSON-string.
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

        // Sample a new partial solution.
        let expected = PartialSolution::new(address, u64::rand(&mut rng), KZGCommitment(rng.gen()));

        // Check the string representation.
        let candidate = format!("{expected}");
        assert_eq!(expected, PartialSolution::from_str(&candidate)?);

        Ok(())
    }
}
