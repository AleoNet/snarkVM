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

#[cfg(feature = "parallel")]
use rayon::prelude::*;

use super::*;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct CombinedPuzzleSolution<N: Network> {
    pub individual_puzzle_solutions: Vec<PartialProverSolution<N>>,
    pub proof: Proof<N::PairingCurve>,
}

impl<N: Network> CombinedPuzzleSolution<N> {
    pub fn new(individual_puzzle_solutions: Vec<PartialProverSolution<N>>, proof: Proof<N::PairingCurve>) -> Self {
        Self { individual_puzzle_solutions, proof }
    }

    pub fn verify(
        &self,
        vk: &CoinbasePuzzleVerifyingKey<N>,
        epoch_info: &EpochInfo,
        epoch_challenge: &EpochChallenge<N>,
    ) -> Result<bool> {
        if self.individual_puzzle_solutions.is_empty() {
            return Ok(false);
        }
        if self.proof.is_hiding() {
            return Ok(false);
        }
        let polynomials: Vec<_> = cfg_iter!(self.individual_puzzle_solutions)
            .map(|solution| {
                // TODO: check difficulty of solution
                CoinbasePuzzle::sample_solution_polynomial(
                    epoch_challenge,
                    epoch_info,
                    solution.address(),
                    solution.nonce(),
                )
            })
            .collect::<Result<Vec<_>>>()?;

        // Compute challenges
        let mut fs_challenges =
            hash_commitments(self.individual_puzzle_solutions.iter().map(|solution| *solution.commitment()));

        let point = match fs_challenges.pop() {
            Some(point) => point,
            None => bail!("Missing challenge point"),
        };

        // Compute combined evaluation
        let mut combined_eval = cfg_iter!(polynomials)
            .zip(&fs_challenges)
            .fold(<N::PairingCurve as PairingEngine>::Fr::zero, |acc, (poly, challenge)| {
                acc + (poly.evaluate(point) * challenge)
            })
            .sum();
        combined_eval *= &epoch_challenge.epoch_polynomial.evaluate(point);

        // Compute combined commitment
        let commitments: Vec<_> =
            cfg_iter!(self.individual_puzzle_solutions).map(|solution| solution.commitment().0).collect();
        let fs_challenges = fs_challenges.into_iter().map(|f| f.to_repr()).collect::<Vec<_>>();
        let combined_commitment = VariableBase::msm(&commitments, &fs_challenges);
        let combined_commitment: Commitment<N::PairingCurve> = Commitment(combined_commitment.into());
        Ok(KZG10::check(vk, &combined_commitment, point, combined_eval, &self.proof)?)
    }
}

impl<N: Network> ToBytes for CombinedPuzzleSolution<N> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        (self.individual_puzzle_solutions.len() as u32).write_le(&mut writer)?;

        for individual_puzzle_solution in &self.individual_puzzle_solutions {
            individual_puzzle_solution.write_le(&mut writer)?;
        }

        self.proof.write_le(&mut writer)
    }
}

impl<N: Network> FromBytes for CombinedPuzzleSolution<N> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let individual_puzzle_solutions_len: u32 = FromBytes::read_le(&mut reader)?;

        let mut individual_puzzle_solutions = Vec::with_capacity(individual_puzzle_solutions_len as usize);
        for _ in 0..individual_puzzle_solutions_len {
            let individual_puzzle_solution: PartialProverSolution<N> = FromBytes::read_le(&mut reader)?;
            individual_puzzle_solutions.push(individual_puzzle_solution);
        }

        let proof = Proof::read_le(&mut reader)?;

        Ok(Self { individual_puzzle_solutions, proof })
    }
}

impl<N: Network> Serialize for CombinedPuzzleSolution<N> {
    /// Serializes the CombinedPuzzleSolution to a JSON-string or buffer.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => {
                let mut combined_puzzle_solution = serializer.serialize_struct("CombinedPuzzleSolution", 3)?;
                combined_puzzle_solution
                    .serialize_field("individual_puzzle_solutions", &self.individual_puzzle_solutions)?;
                combined_puzzle_solution.serialize_field("proof.w", &self.proof.w)?;
                if let Some(random_v) = &self.proof.random_v {
                    combined_puzzle_solution.serialize_field("proof.random_v", &random_v)?;
                }
                combined_puzzle_solution.end()
            }
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for CombinedPuzzleSolution<N> {
    /// Deserializes the CombinedPuzzleSolution from a JSON-string or buffer.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => {
                let combined_puzzle_solution = serde_json::Value::deserialize(deserializer)?;
                Ok(Self::new(
                    serde_json::from_value(combined_puzzle_solution["individual_puzzle_solutions"].clone())
                        .map_err(de::Error::custom)?,
                    Proof {
                        w: serde_json::from_value(combined_puzzle_solution["proof.w"].clone())
                            .map_err(de::Error::custom)?,
                        random_v: match combined_puzzle_solution.get("proof.random_v") {
                            Some(random_v) => {
                                Some(serde_json::from_value(random_v.clone()).map_err(de::Error::custom)?)
                            }
                            None => None,
                        },
                    },
                ))
            }
            false => {
                FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "combined puzzle solution")
            }
        }
    }
}

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
    fn test_serde_json() -> Result<()> {
        let mut rng = TestRng::default();

        // Sample a new combined puzzle solution.
        let mut individual_puzzle_solutions = vec![];
        for _ in 0..rng.gen_range(1..100) {
            let private_key = PrivateKey::<CurrentNetwork>::new(&mut rng)?;
            let address = Address::try_from(private_key)?;

            individual_puzzle_solutions.push(PartialProverSolution::new(
                address,
                u64::rand(&mut rng),
                Commitment(rng.gen()),
            ));
        }
        let expected = CombinedPuzzleSolution::new(individual_puzzle_solutions, Proof { w: rng.gen(), random_v: None });

        // Serialize
        let expected_string = &expected.to_string();
        let candidate_string = serde_json::to_string(&expected)?;
        assert_eq!(expected, serde_json::from_str(&candidate_string)?);

        // Deserialize
        assert_eq!(expected, CombinedPuzzleSolution::from_str(expected_string)?);
        assert_eq!(expected, serde_json::from_str(&candidate_string)?);

        Ok(())
    }

    #[test]
    fn test_bincode() -> Result<()> {
        let mut rng = TestRng::default();

        // Sample a new combined puzzle solution.
        let mut individual_puzzle_solutions = vec![];
        for _ in 0..rng.gen_range(1..100) {
            let private_key = PrivateKey::<CurrentNetwork>::new(&mut rng)?;
            let address = Address::try_from(private_key)?;

            individual_puzzle_solutions.push(PartialProverSolution::new(
                address,
                u64::rand(&mut rng),
                Commitment(rng.gen()),
            ));
        }
        let expected = CombinedPuzzleSolution::new(individual_puzzle_solutions, Proof { w: rng.gen(), random_v: None });

        // Serialize
        let expected_bytes = expected.to_bytes_le()?;
        let expected_bytes_with_size_encoding = bincode::serialize(&expected)?;
        assert_eq!(&expected_bytes[..], &expected_bytes_with_size_encoding[8..]);

        // Deserialize
        assert_eq!(expected, CombinedPuzzleSolution::read_le(&expected_bytes[..])?);
        assert_eq!(expected, bincode::deserialize(&expected_bytes_with_size_encoding[..])?);

        Ok(())
    }
}
