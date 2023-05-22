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

impl<N: Network> FromBytes for CoinbaseSolution<N> {
    /// Reads the coinbase solution from the buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let partial_solutions_len: u32 = FromBytes::read_le(&mut reader)?;

        let mut partial_solutions = Vec::with_capacity(partial_solutions_len as usize);
        for _ in 0..partial_solutions_len {
            let individual_puzzle_solution: PartialSolution<N> = FromBytes::read_le(&mut reader)?;
            partial_solutions.push(individual_puzzle_solution);
        }

        let proof = KZGProof::read_le(&mut reader)?;

        Ok(Self::new(partial_solutions, proof))
    }
}

impl<N: Network> ToBytes for CoinbaseSolution<N> {
    /// Writes the coinbase solution to the buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        (u32::try_from(self.partial_solutions.len()).map_err(|e| error(e.to_string()))?).write_le(&mut writer)?;

        for individual_puzzle_solution in &self.partial_solutions {
            individual_puzzle_solution.write_le(&mut writer)?;
        }

        self.proof.write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::{account::PrivateKey, network::Testnet3};

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_bytes() -> Result<()> {
        let mut rng = TestRng::default();

        // Sample a new coinbase solution.
        let mut partial_solutions = vec![];
        for _ in 0..rng.gen_range(1..10) {
            let private_key = PrivateKey::<CurrentNetwork>::new(&mut rng)?;
            let address = Address::try_from(private_key)?;

            partial_solutions.push(PartialSolution::new(address, u64::rand(&mut rng), KZGCommitment(rng.gen())));
        }
        let expected = CoinbaseSolution::new(partial_solutions, KZGProof { w: rng.gen(), random_v: None });

        // Check the byte representation.
        let expected_bytes = expected.to_bytes_le()?;
        assert_eq!(expected, CoinbaseSolution::read_le(&expected_bytes[..])?);
        // assert!(CoinbaseSolution::<CurrentNetwork>::read_le(&expected_bytes[1..]).is_err());

        Ok(())
    }
}
