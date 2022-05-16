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
use snarkvm_algorithms::prelude::*;
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{CryptoRng, FromBytes, Rng, ToBytes, UniformRand};

use anyhow::{anyhow, bail, Error};
use base58::{FromBase58, ToBase58};
use core::{fmt, str};

pub static ACCOUNT_SK_SIG_DOMAIN: &str = "AleoAccountSignatureSecretKey0";
pub static ACCOUNT_R_SIG_DOMAIN: &str = "AleoAccountSignatureRandomizer0";
pub static ACCOUNT_SK_VRF_DOMAIN: &str = "AleoAccountVRFSecretKey0";

pub static PRIVATE_KEY_PREFIX: [u8; 11] = [127, 134, 189, 116, 210, 221, 210, 137, 145, 18, 253]; // APrivateKey1

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

impl<N: Network> From<&N::Scalar> for PrivateKey<N> {
    /// Returns the account private key from an account seed.
    fn from(seed: &N::Scalar) -> Self {
        // Construct the sk_sig domain separator.
        let sk_sig_input = ACCOUNT_SK_SIG_DOMAIN;
        let sk_sig_domain = N::Scalar::from_bytes_le_mod_order(sk_sig_input.as_bytes());

        // Construct the r_sig domain separator.
        let r_sig_input = format!("{}_{}", ACCOUNT_R_SIG_DOMAIN, 0);
        let r_sig_domain = N::Scalar::from_bytes_le_mod_order(r_sig_input.as_bytes());

        // Construct the sk_vrf domain separator.
        let sk_vrf_input = format!("{}_{}", ACCOUNT_SK_VRF_DOMAIN, 0);
        let sk_vrf_domain = N::Scalar::from_bytes_le_mod_order(sk_vrf_input.as_bytes());

        Self {
            seed: seed.clone(),
            sk_sig: N::AccountPRF::prf(seed, &vec![sk_sig_domain]),
            r_sig: N::AccountPRF::prf(seed, &vec![r_sig_domain]),
            sk_vrf: N::AccountPRF::prf(seed, &vec![sk_vrf_domain]),
        }
    }
}

impl<N: Network> PrivateKey<N> {
    /// Creates a new account private key.
    pub fn new<R: Rng + CryptoRng>(rng: &mut R) -> Self {
        // Sample a random account seed.
        Self::from(&UniformRand::rand(rng))
    }

    //     /// Returns `true` if the private key is well-formed. Otherwise, returns `false`.
    //     pub fn is_valid(&self) -> bool {
    //         self.to_compute_key().is_valid()
    //     }
    //
    //     /// Signs a message using the account private key.
    //     pub fn sign<R: Rng + CryptoRng>(&self, message: &[bool], rng: &mut R) -> Result<N::AccountSignature, AccountError> {
    //         Ok(N::account_signature_scheme().sign(&(self.sk_sig, self.r_sig), message, rng)?.into())
    //     }
    //
    //     /// Returns the address from the private key.
    //     pub fn to_address(&self) -> Address<N> {
    //         Address::from_private_key(self)
    //     }
    //
    //     /// Returns a reference to the account compute key.
    //     pub fn to_compute_key(&self) -> ComputeKey<N> {
    //         ComputeKey::from_private_key(self)
    //     }
    //
    //     /// Returns the decryption key.
    //     pub fn to_decryption_key(&self) -> N::ProgramScalarField {
    //         self.sk_sig + self.r_sig + self.to_compute_key().sk_prf()
    //     }
}

impl<N: Network> str::FromStr for PrivateKey<N> {
    type Err = Error;

    /// Reads in an account private key string.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // Encode the string into base58.
        let data = s.from_base58().map_err(|err| anyhow!("{:?}", err))?;
        if data.len() != 43 {
            bail!("invalid account private key length: found {}, expected 43", data.len())
        } else if data[0..11] != PRIVATE_KEY_PREFIX {
            bail!("Invalid account private key prefix: found {:?}, expected {:?}", &data[0..11], PRIVATE_KEY_PREFIX)
        }
        // Output the private key.
        Ok(Self::from(&FromBytes::read_le(&data[11..43])?))
    }
}

impl<N: Network> fmt::Display for PrivateKey<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Write the private key bytes.
        let mut private_key = [0u8; 43];
        private_key[0..11].copy_from_slice(&PRIVATE_KEY_PREFIX);
        self.seed.write_le(&mut private_key[11..43]).map_err(|_| fmt::Error)?;
        // Encode the private key into base58.
        write!(f, "{}", private_key.to_base58())
    }
}
