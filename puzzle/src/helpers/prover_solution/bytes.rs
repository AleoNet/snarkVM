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

impl<N: Network> FromBytes for ProverSolution<N> {
    /// Reads the prover solution from the buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let partial_solution: PartialSolution<N> = FromBytes::read_le(&mut reader)?;
        let proof = KZGProof::read_le(&mut reader)?;

        Ok(Self::new(partial_solution, proof))
    }
}

impl<N: Network> ToBytes for ProverSolution<N> {
    /// Writes the prover solution to the buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.partial_solution.write_le(&mut writer)?;
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
        let private_key = PrivateKey::<CurrentNetwork>::new(&mut rng)?;
        let address = Address::try_from(private_key)?;

        // Sample a new prover solution.
        let partial_solution = PartialSolution::new(address, u64::rand(&mut rng), KZGCommitment(rng.gen()));
        let expected = ProverSolution::new(partial_solution, KZGProof { w: rng.gen(), random_v: None });

        // Check the byte representation.
        let expected_bytes = expected.to_bytes_le()?;
        assert_eq!(expected, ProverSolution::read_le(&expected_bytes[..])?);
        assert!(ProverSolution::<CurrentNetwork>::read_le(&expected_bytes[1..]).is_err());

        Ok(())
    }
}
