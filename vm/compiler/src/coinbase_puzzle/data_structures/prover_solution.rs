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

#[derive(Copy, Clone)]
pub struct ProverPuzzleSolution<N: Network> {
    pub partial_solution: PartialProverSolution<N>,
    pub proof: Proof<N::PairingCurve>,
}

impl<N: Network> ProverPuzzleSolution<N> {
    pub fn new(partial_solution: PartialProverSolution<N>, proof: Proof<N::PairingCurve>) -> Self {
        Self { partial_solution, proof }
    }

    pub fn verify(
        &self,
        vk: &CoinbasePuzzleVerifyingKey<N>,
        epoch_info: &EpochInfo,
        epoch_challenge: &EpochChallenge<N>,
    ) -> Result<bool> {
        if self.proof.is_hiding() {
            return Ok(false);
        }

        let polynomial =
            CoinbasePuzzle::sample_solution_polynomial(epoch_challenge, epoch_info, self.address(), self.nonce())?;
        let point = hash_commitment(self.commitment());
        let epoch_challenge_eval = epoch_challenge.epoch_polynomial.evaluate(point);
        let polynomial_eval = polynomial.evaluate(point);
        let product_eval = epoch_challenge_eval * polynomial_eval;
        Ok(KZG10::check(vk, self.commitment(), point, product_eval, self.proof())?)
    }

    pub fn address(&self) -> &Address<N> {
        self.partial_solution.address()
    }

    pub fn nonce(&self) -> u64 {
        self.partial_solution.nonce()
    }

    pub fn commitment(&self) -> &Commitment<N::PairingCurve> {
        self.partial_solution.commitment()
    }

    pub fn proof(&self) -> &Proof<N::PairingCurve> {
        &self.proof
    }
}

impl<N: Network> Eq for ProverPuzzleSolution<N> {}

impl<N: Network> PartialEq for ProverPuzzleSolution<N> {
    /// Implements the `Eq` trait for the ProverPuzzleSolution.
    fn eq(&self, other: &Self) -> bool {
        self.partial_solution == other.partial_solution && self.proof == other.proof
    }
}

// TODO (raychu86): Use derive Hash. It seems commitment and proof do not derive it properly.
impl<N: Network> core::hash::Hash for ProverPuzzleSolution<N> {
    /// Implements the `Hash` trait for the ProverPuzzleSolution.
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.partial_solution.hash(state);
        self.proof.w.hash(state);
        self.proof.random_v.hash(state);
    }
}

impl<N: Network> ToBytes for ProverPuzzleSolution<N> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.partial_solution.write_le(&mut writer)?;
        self.proof.write_le(&mut writer)
    }
}

impl<N: Network> FromBytes for ProverPuzzleSolution<N> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let partial_solution: PartialProverSolution<N> = FromBytes::read_le(&mut reader)?;
        let proof = Proof::read_le(&mut reader)?;

        Ok(Self { partial_solution, proof })
    }
}

impl<N: Network> Serialize for ProverPuzzleSolution<N> {
    /// Serializes the ProverPuzzleSolution to a JSON-string or buffer.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => {
                let mut prover_puzzle_solution = serializer.serialize_struct("ProverPuzzleSolution", 3)?;
                prover_puzzle_solution.serialize_field("partial_solution", &self.partial_solution)?;
                prover_puzzle_solution.serialize_field("proof.w", &self.proof.w)?;
                if let Some(random_v) = &self.proof.random_v {
                    prover_puzzle_solution.serialize_field("proof.random_v", &random_v)?;
                }
                prover_puzzle_solution.end()
            }
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for ProverPuzzleSolution<N> {
    /// Deserializes the ProverPuzzleSolution from a JSON-string or buffer.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => {
                let prover_puzzle_solution = serde_json::Value::deserialize(deserializer)?;
                Ok(Self::new(
                    serde_json::from_value(prover_puzzle_solution["partial_solution"].clone())
                        .map_err(de::Error::custom)?,
                    Proof {
                        w: serde_json::from_value(prover_puzzle_solution["proof.w"].clone())
                            .map_err(de::Error::custom)?,
                        random_v: match prover_puzzle_solution.get("proof.random_v") {
                            Some(random_v) => {
                                Some(serde_json::from_value(random_v.clone()).map_err(de::Error::custom)?)
                            }
                            None => None,
                        },
                    },
                ))
            }
            false => {
                FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "prover puzzle solution")
            }
        }
    }
}

impl<N: Network> FromStr for ProverPuzzleSolution<N> {
    type Err = Error;

    /// Initializes the ProverPuzzleSolution from a JSON-string.
    fn from_str(partial_prover_solution: &str) -> Result<Self, Self::Err> {
        Ok(serde_json::from_str(partial_prover_solution)?)
    }
}

impl<N: Network> Debug for ProverPuzzleSolution<N> {
    /// Prints the ProverPuzzleSolution as a JSON-string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for ProverPuzzleSolution<N> {
    /// Displays the ProverPuzzleSolution as a JSON-string.
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
        let rng = &mut rand::thread_rng();
        let private_key = PrivateKey::<CurrentNetwork>::new(rng)?;
        let address = Address::try_from(private_key)?;

        // Sample a new prover puzzle solution.
        let partial_prover_solution = PartialProverSolution::new(address, u64::rand(rng), Commitment(rng.gen()));
        let expected = ProverPuzzleSolution::new(partial_prover_solution, Proof { w: rng.gen(), random_v: None });

        // Serialize
        let expected_string = &expected.to_string();
        let candidate_string = serde_json::to_string(&expected)?;
        assert_eq!(expected, serde_json::from_str(&candidate_string)?);

        // Deserialize
        assert_eq!(expected, ProverPuzzleSolution::from_str(expected_string)?);
        assert_eq!(expected, serde_json::from_str(&candidate_string)?);

        Ok(())
    }

    #[test]
    fn test_bincode() -> Result<()> {
        let rng = &mut rand::thread_rng();
        let private_key = PrivateKey::<CurrentNetwork>::new(rng)?;
        let address = Address::try_from(private_key)?;

        // Sample a new prover puzzle solution.
        let partial_prover_solution = PartialProverSolution::new(address, u64::rand(rng), Commitment(rng.gen()));
        let expected = ProverPuzzleSolution::new(partial_prover_solution, Proof { w: rng.gen(), random_v: None });

        // Serialize
        let expected_bytes = expected.to_bytes_le()?;
        let expected_bytes_with_size_encoding = bincode::serialize(&expected)?;
        assert_eq!(&expected_bytes[..], &expected_bytes_with_size_encoding[8..]);

        // Deserialize
        assert_eq!(expected, ProverPuzzleSolution::read_le(&expected_bytes[..])?);
        assert_eq!(expected, bincode::deserialize(&expected_bytes_with_size_encoding[..])?);

        Ok(())
    }
}
