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

#[cfg(test)]
mod tests {
    use super::*;
    use console::{account::PrivateKey, network::Testnet3};

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_bytes() -> Result<()> {
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

        // Check the byte representation.
        let expected_bytes = expected.to_bytes_le()?;
        assert_eq!(expected, CombinedPuzzleSolution::read_le(&expected_bytes[..])?);
        // assert!(CombinedPuzzleSolution::<CurrentNetwork>::read_le(&expected_bytes[1..]).is_err());

        Ok(())
    }
}
