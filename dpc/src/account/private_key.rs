// Copyright (C) 2019-2021 Aleo Systems Inc.
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

use crate::{account_format, AccountError, ComputeKey, Parameters};
use snarkvm_algorithms::traits::{SignatureScheme, PRF};
use snarkvm_fields::{One, Zero};
use snarkvm_utilities::{FromBytes, ToBytes, UniformRand};

use base58::{FromBase58, ToBase58};
use rand::{CryptoRng, Rng};
use std::{fmt, str::FromStr};

#[derive(Derivative)]
#[derivative(
    Clone(bound = "C: Parameters"),
    PartialEq(bound = "C: Parameters"),
    Eq(bound = "C: Parameters")
)]
pub struct PrivateKey<C: Parameters> {
    seed: C::AccountSeed,
    // Derived private attributes from the seed.
    sk_sig: <C::AccountSignatureScheme as SignatureScheme>::PrivateKey,
    compute_key: ComputeKey<C>,
}

impl<C: Parameters> PrivateKey<C> {
    /// Creates a new account private key.
    pub fn new<R: Rng + CryptoRng>(rng: &mut R) -> Self {
        // Sample randomly until a valid private key is found.
        loop {
            // Samples a random account seed, and returns the private key if it is valid.
            if let Ok(private_key) = Self::from_seed(&C::AccountSeed::rand(rng)) {
                return private_key;
            }
        }
    }

    /// Derives the account private key from a given seed and verifies it is well-formed.
    pub fn from_seed(seed: &C::AccountSeed) -> Result<Self, AccountError> {
        // Generate the signature private key.
        let sk_sig: <C::AccountSignatureScheme as SignatureScheme>::PrivateKey =
            C::AccountPRF::evaluate(&seed, &C::ProgramScalarField::zero())?;

        // Derive the signature public key.
        let pk_sig = C::account_signature_scheme().generate_public_key(&sk_sig)?;

        // Generate the PRF secret key.
        let sk_prf: <C::SerialNumberPRF as PRF>::Seed = C::AccountPRF::evaluate(&seed, &C::ProgramScalarField::one())?;

        // Initialize the compute key.
        let compute_key = ComputeKey::new(pk_sig, sk_prf)?;

        Ok(Self {
            seed: *seed,
            sk_sig,
            compute_key,
        })
    }

    /// Returns `true` if the private key is well-formed. Otherwise, returns `false`.
    pub fn is_valid(&self) -> bool {
        self.compute_key.is_valid()
    }

    /// Returns a reference to the signature private key.
    pub fn sk_sig(&self) -> &<C::AccountSignatureScheme as SignatureScheme>::PrivateKey {
        &self.sk_sig
    }

    /// Returns a reference to the compute key.
    pub fn compute_key(&self) -> &ComputeKey<C> {
        &self.compute_key
    }
}

impl<C: Parameters> FromStr for PrivateKey<C> {
    type Err = AccountError;

    /// Reads in an account private key string.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let data = s.from_base58()?;
        if data.len() != 41 {
            return Err(AccountError::InvalidByteLength(data.len()));
        }

        if data[0..9] != account_format::PRIVATE_KEY_PREFIX {
            return Err(AccountError::InvalidPrefixBytes(data[0..9].to_vec()));
        }

        Self::from_seed(&FromBytes::read_le(&data[9..41])?)
    }
}

impl<C: Parameters> fmt::Display for PrivateKey<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut private_key = [0u8; 41];
        private_key[0..9].copy_from_slice(&account_format::PRIVATE_KEY_PREFIX);

        self.seed
            .write_le(&mut private_key[9..41])
            .expect("seed formatting failed");

        write!(f, "{}", private_key.to_base58())
    }
}

impl<C: Parameters> fmt::Debug for PrivateKey<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "PrivateKey {{ seed: {:?} }}", self.seed)
    }
}
