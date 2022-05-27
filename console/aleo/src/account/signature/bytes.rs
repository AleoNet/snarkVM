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

impl<N: Network> FromBytes for Signature<N> {
    /// Reads an account signature from a buffer.
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let challenge = N::Scalar::read_le(&mut reader)?;
        let response = N::Scalar::read_le(&mut reader)?;
        let compute_key = ComputeKey::read_le(&mut reader)?;
        Ok(Self { challenge, response, compute_key })
    }
}

impl<N: Network> ToBytes for Signature<N> {
    /// Writes an account signature to a buffer.
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.challenge.write_le(&mut writer)?;
        self.response.write_le(&mut writer)?;
        self.compute_key.write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::PrivateKey;
    use snarkvm_console_network::Testnet3;
    use snarkvm_utilities::{test_crypto_rng, UniformRand};

    use anyhow::Result;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: u64 = 1000;

    #[test]
    fn test_bytes() -> Result<()> {
        for i in 0..ITERATIONS {
            // Sample an address and a private key.
            let private_key = PrivateKey::<CurrentNetwork>::new(&mut test_crypto_rng())?;
            let address = Address::try_from(&private_key)?;

            // Generate a signature.
            let message: Vec<bool> = (0..(32 * i)).map(|_| rand::random::<bool>()).collect();
            let randomizer = UniformRand::rand(&mut test_crypto_rng());
            let signature = Signature::sign(&private_key, &message, randomizer)?;
            assert!(signature.verify(&address, &message));

            // Check the byte representation.
            let signature_bytes = signature.to_bytes_le()?;
            assert_eq!(signature, Signature::read_le(&signature_bytes[..])?);
            assert!(Signature::<CurrentNetwork>::read_le(&signature_bytes[1..]).is_err());
        }
        Ok(())
    }
}
