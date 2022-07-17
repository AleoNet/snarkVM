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
        let challenge = Scalar::new(FromBytes::read_le(&mut reader)?);
        let response = Scalar::new(FromBytes::read_le(&mut reader)?);
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
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: u64 = 100;

    #[test]
    fn test_bytes() -> Result<()> {
        for i in 0..ITERATIONS {
            // Sample a new signature.
            let signature = test_helpers::sample_signature(i);

            // Check the byte representation.
            let signature_bytes = signature.to_bytes_le()?;
            assert_eq!(signature, Signature::read_le(&signature_bytes[..])?);
            assert!(Signature::<CurrentNetwork>::read_le(&signature_bytes[1..]).is_err());
        }
        Ok(())
    }
}
