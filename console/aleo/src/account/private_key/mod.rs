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

use crate::Network;
use snarkvm_console_algorithms::{Poseidon2, PRF};
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{
    error,
    io::{Read, Result as IoResult, Write},
    CryptoRng,
    FromBytes,
    FromBytesDeserializer,
    Rng,
    ToBytes,
    ToBytesSerializer,
    UniformRand,
};

use anyhow::{anyhow, bail, Error, Result};
use base58::{FromBase58, ToBase58};
use core::{fmt, str::FromStr};
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};

static ACCOUNT_SK_SIG_DOMAIN: &str = "AleoAccountSignatureSecretKey0";
static ACCOUNT_R_SIG_DOMAIN: &str = "AleoAccountSignatureRandomizer0";
static ACCOUNT_SK_VRF_DOMAIN: &str = "AleoAccountVRFSecretKey0";
static PRIVATE_KEY_PREFIX: [u8; 11] = [127, 134, 189, 116, 210, 221, 210, 137, 145, 18, 253]; // APrivateKey1

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct PrivateKey<N: Network> {
    /// The private key.
    seed: N::Scalar,
    /// The derived signature secret key.
    sk_sig: N::Scalar,
    /// The derived signature randomizer.
    r_sig: N::Scalar,
    /// The derived VRF secret key.
    sk_vrf: N::Scalar,
}

impl<N: Network> PrivateKey<N> {
    /// Samples a new random private key.
    #[inline]
    pub fn new<R: Rng + CryptoRng>(rng: &mut R) -> Result<Self> {
        // Sample a random account seed.
        Self::try_from(UniformRand::rand(rng))
    }

    /// Returns the account private key from an account seed.
    #[inline]
    pub fn try_from(seed: N::Scalar) -> Result<Self> {
        // Construct the sk_sig domain separator.
        let sk_sig_input = ACCOUNT_SK_SIG_DOMAIN;
        let sk_sig_domain = N::Scalar::from_bytes_le_mod_order(sk_sig_input.as_bytes());

        // Construct the r_sig domain separator.
        let r_sig_input = format!("{}.{}", ACCOUNT_R_SIG_DOMAIN, 0);
        let r_sig_domain = N::Scalar::from_bytes_le_mod_order(r_sig_input.as_bytes());

        // Construct the sk_vrf domain separator.
        let sk_vrf_input = format!("{}.{}", ACCOUNT_SK_VRF_DOMAIN, 0);
        let sk_vrf_domain = N::Scalar::from_bytes_le_mod_order(sk_vrf_input.as_bytes());

        // Initialize Poseidon2 on the **scalar** field.
        let poseidon2 = Poseidon2::<N::Scalar>::setup();

        Ok(Self {
            seed,
            sk_sig: poseidon2.prf(&seed, &[sk_sig_domain])?,
            r_sig: poseidon2.prf(&seed, &[r_sig_domain])?,
            sk_vrf: poseidon2.prf(&seed, &[sk_vrf_domain])?,
        })
    }

    /// Returns the signature secret key.
    pub const fn sk_sig(&self) -> &N::Scalar {
        &self.sk_sig
    }

    /// Returns the signature randomizer.
    pub const fn r_sig(&self) -> &N::Scalar {
        &self.r_sig
    }

    /// Returns the VRF secret key.
    pub const fn sk_vrf(&self) -> &N::Scalar {
        &self.sk_vrf
    }
}

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
        Ok(Self::try_from(FromBytes::read_le(&data[11..43])?).map_err(|e| error(format!("{e}")))?)
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

impl<N: Network> FromBytes for PrivateKey<N> {
    /// Reads an account private key from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self::try_from(FromBytes::read_le(&mut reader)?).map_err(|e| error(format!("{e}")))?)
    }
}

impl<N: Network> ToBytes for PrivateKey<N> {
    /// Writes an account private key to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.seed.write_le(&mut writer)
    }
}

impl<N: Network> Serialize for PrivateKey<N> {
    /// Serializes an account private key into string or bytes.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => serializer.collect_str(self),
            false => ToBytesSerializer::serialize(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for PrivateKey<N> {
    /// Deserializes an account private key from a string or bytes.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => FromStr::from_str(&String::deserialize(deserializer)?).map_err(de::Error::custom),
            false => FromBytesDeserializer::<Self>::deserialize(
                deserializer,
                "private key",
                (N::Scalar::size_in_bits() + 7) / 8,
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{PrivateKey, Testnet3};
    use snarkvm_utilities::test_crypto_rng;

    use anyhow::Result;

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
        }
        Ok(())
    }

    #[test]
    fn test_serde_json() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a new private key.
            let expected = PrivateKey::<CurrentNetwork>::new(&mut test_crypto_rng())?;

            // Serialize
            let expected_string = &expected.to_string();
            let candidate_string = serde_json::to_string(&expected)?;
            assert_eq!(expected_string, serde_json::Value::from_str(&candidate_string)?.as_str().unwrap());

            // Deserialize
            assert_eq!(expected, PrivateKey::from_str(expected_string)?);
            assert_eq!(expected, serde_json::from_str(&candidate_string)?);
        }
        Ok(())
    }

    #[test]
    fn test_bincode() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a new private key.
            let expected = PrivateKey::<CurrentNetwork>::new(&mut test_crypto_rng())?;

            // Serialize
            let expected_bytes = expected.to_bytes_le()?;
            assert_eq!(&expected_bytes[..], &bincode::serialize(&expected)?[..]);

            // Deserialize
            assert_eq!(expected, PrivateKey::read_le(&expected_bytes[..])?);
            assert_eq!(expected, bincode::deserialize(&expected_bytes[..])?);
        }
        Ok(())
    }
}
