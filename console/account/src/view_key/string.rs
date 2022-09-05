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

static VIEW_KEY_PREFIX: [u8; 7] = [14, 138, 223, 204, 247, 224, 122]; // AViewKey1

impl<N: Network> FromStr for ViewKey<N> {
    type Err = Error;

    /// Reads in an account view key from a base58 string.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // Encode the string into base58.
        let data = s.from_base58().map_err(|err| anyhow!("{:?}", err))?;
        if data.len() != 39 {
            bail!("Invalid account view key length: found {}, expected 39", data.len())
        } else if data[0..7] != VIEW_KEY_PREFIX {
            bail!("Invalid account view key prefix: found {:?}, expected {:?}", &data[0..7], VIEW_KEY_PREFIX)
        }
        // Output the view key.
        Ok(Self::from_scalar(Scalar::new(FromBytes::read_le(&data[7..39])?)))
    }
}

impl<N: Network> fmt::Display for ViewKey<N> {
    /// Writes the account view key as a base58 string.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Write the view key bytes.
        let mut view_key = [0u8; 39];
        view_key[0..7].copy_from_slice(&VIEW_KEY_PREFIX);
        self.0.write_le(&mut view_key[7..39]).map_err(|_| fmt::Error)?;
        // Encode the view key into base58.
        write!(f, "{}", view_key.to_base58())
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
            // Sample a new view key.
            let private_key = PrivateKey::<CurrentNetwork>::new(&mut test_crypto_rng())?;
            let expected = ViewKey::try_from(private_key)?;

            // Check the string representation.
            let candidate = format!("{expected}");
            assert_eq!(expected, ViewKey::from_str(&candidate)?);
            assert_eq!("AViewKey", candidate.split('1').next().unwrap());
        }
        Ok(())
    }
}
