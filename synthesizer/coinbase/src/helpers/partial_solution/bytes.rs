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

impl<N: Network> FromBytes for PartialSolution<N> {
    /// Reads the partial solution from the buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let address: Address<N> = FromBytes::read_le(&mut reader)?;
        let nonce = u64::read_le(&mut reader)?;
        let commitment = KZGCommitment::read_le(&mut reader)?;

        Ok(Self::new(address, nonce, commitment))
    }
}

impl<N: Network> ToBytes for PartialSolution<N> {
    /// Writes the partial solution to the buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.address.write_le(&mut writer)?;
        self.nonce.write_le(&mut writer)?;
        self.commitment.write_le(&mut writer)
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

        // Sample a new partial solution.
        let expected = PartialSolution::new(address, u64::rand(&mut rng), KZGCommitment(rng.gen()));

        // Check the byte representation.
        let expected_bytes = expected.to_bytes_le()?;
        assert_eq!(expected, PartialSolution::read_le(&expected_bytes[..])?);
        assert!(PartialSolution::<CurrentNetwork>::read_le(&expected_bytes[1..]).is_err());

        Ok(())
    }
}
