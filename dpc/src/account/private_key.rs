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

use crate::{
    account_format,
    AccountError,
    Address,
    ComputeKey,
    Network,
    ACCOUNT_SEED_R_SIG_DOMAIN,
    ACCOUNT_SEED_SK_SIG_DOMAIN,
};
use snarkvm_algorithms::traits::{SignatureScheme, PRF};
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{FromBytes, ToBytes, Uniform};

use base58::{FromBase58, ToBase58};
use rand::{CryptoRng, Rng};
use std::{fmt, str::FromStr};

#[derive(Clone, PartialEq, Eq)]
pub struct PrivateKey<N: Network> {
    seed: N::AccountSeed,
    pub(super) sk_sig: N::ProgramScalarField,
    pub(super) r_sig: N::ProgramScalarField,
}

impl<N: Network> PrivateKey<N> {
    /// Creates a new account private key.
    pub fn new<R: Rng + CryptoRng>(rng: &mut R) -> Self {
        // Sample a random account seed.
        Self::from(&N::AccountSeed::rand(rng))
    }

    /// Returns `true` if the private key is well-formed. Otherwise, returns `false`.
    pub fn is_valid(&self) -> bool {
        self.to_compute_key().is_valid()
    }

    /// Signs a message using the account private key.
    pub fn sign<R: Rng + CryptoRng>(&self, message: &[bool], rng: &mut R) -> Result<N::AccountSignature, AccountError> {
        Ok(N::account_signature_scheme().sign(&(self.sk_sig, self.r_sig), message, rng)?.into())
    }

    /// Returns the address from the private key.
    pub fn to_address(&self) -> Address<N> {
        Address::from_private_key(self)
    }

    /// Returns a reference to the account compute key.
    pub fn to_compute_key(&self) -> ComputeKey<N> {
        ComputeKey::from_private_key(self)
    }

    /// Returns the decryption key.
    pub fn to_decryption_key(&self) -> N::ProgramScalarField {
        self.sk_sig + self.r_sig + self.to_compute_key().sk_prf()
    }
}

impl<N: Network> From<&N::AccountSeed> for PrivateKey<N> {
    /// Returns the account private key from an account seed.
    fn from(seed: &N::AccountSeed) -> Self {
        // Construct the sk_sig domain separator.
        let sk_sig_input = ACCOUNT_SEED_SK_SIG_DOMAIN;
        let sk_sig_domain = N::ProgramScalarField::from_bytes_le_mod_order(sk_sig_input.as_bytes());

        // Construct the r_sig domain separator.
        let r_sig_input = format!("{}_{}", ACCOUNT_SEED_R_SIG_DOMAIN, 0);
        let r_sig_domain = N::ProgramScalarField::from_bytes_le_mod_order(r_sig_input.as_bytes());

        Self {
            seed: seed.clone(),
            sk_sig: N::AccountSeedPRF::prf(seed, &vec![sk_sig_domain]),
            r_sig: N::AccountSeedPRF::prf(seed, &vec![r_sig_domain]),
        }
    }
}

impl<N: Network> FromStr for PrivateKey<N> {
    type Err = AccountError;

    /// Reads in an account private key string.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let data = s.from_base58()?;
        if data.len() != 43 {
            return Err(AccountError::InvalidByteLength(data.len()));
        }

        if data[0..11] != account_format::PRIVATE_KEY_PREFIX {
            return Err(AccountError::InvalidPrefixBytes(data[0..11].to_vec()));
        }

        Ok(Self::from(&FromBytes::read_le(&data[11..43])?))
    }
}

impl<N: Network> fmt::Display for PrivateKey<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut private_key = [0u8; 43];
        private_key[0..11].copy_from_slice(&account_format::PRIVATE_KEY_PREFIX);
        self.seed.write_le(&mut private_key[11..43]).expect("seed formatting failed");

        write!(f, "{}", private_key.to_base58())
    }
}

impl<N: Network> fmt::Debug for PrivateKey<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "PrivateKey {{ seed: {:?} }}", self.seed)
    }
}
