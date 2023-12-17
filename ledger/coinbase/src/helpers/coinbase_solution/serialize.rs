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

use snarkvm_utilities::DeserializeExt;

impl<N: Network> Serialize for CoinbaseSolution<N> {
    /// Serializes the solutions to a JSON-string or buffer.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => {
                let mut solutions = serializer.serialize_struct("CoinbaseSolution", 1)?;
                solutions.serialize_field("solutions", &self.solutions.values().collect::<Vec<_>>())?;
                solutions.end()
            }
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for CoinbaseSolution<N> {
    /// Deserializes the solutions from a JSON-string or buffer.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => {
                let mut solutions = serde_json::Value::deserialize(deserializer)?;
                Self::new(DeserializeExt::take_from_value::<D>(&mut solutions, "solutions")?).map_err(de::Error::custom)
            }
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "solutions"),
        }
    }
}

#[cfg(test)]
pub(super) mod tests {
    use super::*;
    use console::account::PrivateKey;

    type CurrentNetwork = console::network::Testnet3;

    pub(crate) fn sample_solutions(rng: &mut TestRng) -> CoinbaseSolution<CurrentNetwork> {
        // Sample a new solutions.
        let mut prover_solutions = vec![];
        for _ in 0..rng.gen_range(1..10) {
            let private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
            let address = Address::try_from(private_key).unwrap();

            let partial_solution = PartialSolution::new(address, u64::rand(rng), KZGCommitment(rng.gen()));
            prover_solutions.push(ProverSolution::new(partial_solution, KZGProof { w: rng.gen(), random_v: None }));
        }
        CoinbaseSolution::new(prover_solutions).unwrap()
    }

    #[test]
    fn test_serde_json() -> Result<()> {
        let rng = &mut TestRng::default();

        // Sample a new solutions.
        let expected = sample_solutions(rng);

        // Serialize
        let expected_string = &expected.to_string();
        let candidate_string = serde_json::to_string(&expected)?;
        assert_eq!(expected, serde_json::from_str(&candidate_string)?);

        // Deserialize
        assert_eq!(expected, CoinbaseSolution::from_str(expected_string)?);
        assert_eq!(expected, serde_json::from_str(&candidate_string)?);

        Ok(())
    }

    #[test]
    fn test_bincode() -> Result<()> {
        let rng = &mut TestRng::default();

        // Sample a new solutions.
        let expected = sample_solutions(rng);

        // Serialize
        let expected_bytes = expected.to_bytes_le()?;
        let expected_bytes_with_size_encoding = bincode::serialize(&expected)?;
        assert_eq!(&expected_bytes[..], &expected_bytes_with_size_encoding[8..]);

        // Deserialize
        assert_eq!(expected, CoinbaseSolution::read_le(&expected_bytes[..])?);
        assert_eq!(expected, bincode::deserialize(&expected_bytes_with_size_encoding[..])?);

        Ok(())
    }
}
