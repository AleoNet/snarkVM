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

static PRIVATE_KEY_PREFIX: [u8; 11] = [127, 134, 189, 116, 210, 221, 210, 137, 145, 18, 253]; // APrivateKey1

impl<N: Network> FromStr for PrivateKey<N> {
    type Err = Error;

    /// Reads in an account private key from a base58 string.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // Encode the string into base58.
        let data = s.from_base58().map_err(|err| anyhow!("{:?}", err))?;
        if data.len() != 43 {
            bail!("Invalid account private key length: found {}, expected 43", data.len())
        } else if data[0..11] != PRIVATE_KEY_PREFIX {
            bail!("Invalid account private key prefix: found {:?}, expected {:?}", &data[0..11], PRIVATE_KEY_PREFIX)
        }
        // Output the private key.
        Ok(Self::try_from(Field::new(FromBytes::read_le(&data[11..43])?)).map_err(|e| error(format!("{e}")))?)
    }
}

impl<N: Network> fmt::Display for PrivateKey<N> {
    /// Writes the account private key as a base58 string.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Write the private key bytes.
        let mut private_key = [0u8; 43];
        private_key[0..11].copy_from_slice(&PRIVATE_KEY_PREFIX);
        self.seed.write_le(&mut private_key[11..43]).map_err(|_| fmt::Error)?;
        // Encode the private key into base58.
        write!(f, "{}", private_key.to_base58())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: u64 = 1000;

    #[test]
    fn test_string() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a new private key.
            let expected = PrivateKey::<CurrentNetwork>::new(&mut test_crypto_rng())?;

            // Check the string representation.
            let candidate = format!("{expected}");
            assert_eq!(expected, PrivateKey::from_str(&candidate)?);
            assert_eq!("APrivateKey", candidate.split('1').next().unwrap());
        }
        Ok(())
    }
}
