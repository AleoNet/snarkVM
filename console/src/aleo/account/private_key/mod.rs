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

use crate::{aleo::Network, algorithms::PRF};
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{error, CryptoRng, FromBytes, Rng, ToBytes, UniformRand};

use crate::algorithms::Poseidon2;
use anyhow::{anyhow, bail, Error, Result};
use base58::{FromBase58, ToBase58};
use core::{fmt, str::FromStr};

static ACCOUNT_SK_SIG_DOMAIN: &str = "AleoAccountSignatureSecretKey0";
static ACCOUNT_R_SIG_DOMAIN: &str = "AleoAccountSignatureRandomizer0";
static ACCOUNT_SK_VRF_DOMAIN: &str = "AleoAccountVRFSecretKey0";
static PRIVATE_KEY_PREFIX: [u8; 11] = [127, 134, 189, 116, 210, 221, 210, 137, 145, 18, 253]; // APrivateKey1

#[derive(Clone, Debug, PartialEq, Eq)]
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

// impl<N: Network> TryFrom<N::Scalar> for PrivateKey<N> {
//     type Error = Error;
//
//     /// Returns the account private key from an account seed.
//     fn try_from(seed: N::Scalar) -> Result<Self, Self::Error> {
//         Self::try_from(&seed)
//     }
// }

// impl<N: Network> TryFrom<&N::Scalar> for PrivateKey<N> {
//     type Error = Error;
//
//     /// Returns the account private key from an account seed.
//     fn try_from(seed: &N::Scalar) -> Result<Self, Self::Error> {
//         // Construct the sk_sig domain separator.
//         let sk_sig_input = ACCOUNT_SK_SIG_DOMAIN;
//         let sk_sig_domain = N::Scalar::from_bytes_le_mod_order(sk_sig_input.as_bytes());
//
//         // Construct the r_sig domain separator.
//         let r_sig_input = format!("{}.{}", ACCOUNT_R_SIG_DOMAIN, 0);
//         let r_sig_domain = N::Scalar::from_bytes_le_mod_order(r_sig_input.as_bytes());
//
//         // Construct the sk_vrf domain separator.
//         let sk_vrf_input = format!("{}.{}", ACCOUNT_SK_VRF_DOMAIN, 0);
//         let sk_vrf_domain = N::Scalar::from_bytes_le_mod_order(sk_vrf_input.as_bytes());
//
//         Ok(Self {
//             seed: *seed,
//             sk_sig: N::prf_psd2(seed, &[sk_sig_domain]),
//             r_sig: N::prf_psd2(seed, &[r_sig_domain]),
//             sk_vrf: N::prf_psd2(seed, &[sk_vrf_domain]),
//         })
//     }
// }

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
    pub(super) fn sk_sig(&self) -> &N::Scalar {
        &self.sk_sig
    }

    /// Returns the signature randomizer.
    pub(super) fn r_sig(&self) -> &N::Scalar {
        &self.r_sig
    }

    /// Returns the VRF secret key.
    pub(super) fn sk_vrf(&self) -> &N::Scalar {
        &self.sk_vrf
    }

    //     /// Signs a message using the account private key.
    //     pub fn sign<R: Rng + CryptoRng>(&self, message: &[bool], rng: &mut R) -> Result<N::AccountSignature, AccountError> {
    //         Ok(N::account_signature_scheme().sign(&(self.sk_sig, self.r_sig), message, rng)?.into())
    //     }
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
