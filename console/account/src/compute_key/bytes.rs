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

impl<N: Network> FromBytes for ComputeKey<N> {
    /// Reads an account compute key from a buffer.
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let pk_sig =
            Group::from_x_coordinate(Field::new(N::Field::read_le(&mut reader)?)).map_err(|e| error(format!("{e}")))?;
        let pr_sig =
            Group::from_x_coordinate(Field::new(N::Field::read_le(&mut reader)?)).map_err(|e| error(format!("{e}")))?;
        Self::try_from((pk_sig, pr_sig)).map_err(|e| error(format!("{e}")))
    }
}

impl<N: Network> ToBytes for ComputeKey<N> {
    /// Writes an account compute key to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.pk_sig.to_x_coordinate().write_le(&mut writer)?;
        self.pr_sig.to_x_coordinate().write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: u64 = 1000;

    #[test]
    fn test_bytes() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a new compute key.
            let private_key = PrivateKey::<CurrentNetwork>::new(&mut test_crypto_rng())?;
            let expected = ComputeKey::try_from(private_key)?;

            // Check the byte representation.
            let expected_bytes = expected.to_bytes_le()?;
            assert_eq!(expected, ComputeKey::read_le(&expected_bytes[..])?);
            assert!(ComputeKey::<CurrentNetwork>::read_le(&expected_bytes[1..]).is_err());
        }
        Ok(())
    }
}
