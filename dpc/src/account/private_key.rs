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
use snarkvm_algorithms::traits::{CryptoHash, SignatureScheme, PRF};
use snarkvm_fields::Field;
use snarkvm_utilities::{FromBytes, ToBytes, UniformRand};

use anyhow::{anyhow, Result};
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
    sk_sig: <C::AccountSignatureScheme as SignatureScheme>::PrivateKey,
}

impl<C: Parameters> PrivateKey<C> {
    /// Creates a new account private key.
    pub fn new<R: Rng + CryptoRng>(rng: &mut R) -> Self {
        // Sample a random signature private key.
        Self::from(<C::AccountSignatureScheme as SignatureScheme>::PrivateKey::rand(rng))
    }

    /// Returns the account private key from a signature private key.
    pub fn from(sk_sig: <C::AccountSignatureScheme as SignatureScheme>::PrivateKey) -> Self {
        Self { sk_sig }
    }

    /// Returns a reference to the signature private key.
    pub fn sk_sig(&self) -> &<C::AccountSignatureScheme as SignatureScheme>::PrivateKey {
        &self.sk_sig
    }

    /// Returns the compute key.
    pub fn to_compute_key(&self) -> Result<ComputeKey<C>> {
        // Derive the signature public key.
        let pk_sig = C::account_signature_scheme().generate_public_key(&self.sk_sig)?;

        // Generate the PRF secret key.
        let sk_prf: <C::SerialNumberPRF as PRF>::Seed = {
            let output_fq = C::AccountCryptoHash::evaluate(&[pk_sig])?;
            match C::ProgramScalarField::from_random_bytes(&output_fq.to_bytes_le()?) {
                Some(output_fr) => FromBytes::read_le(&output_fr.to_bytes_le()?[..])?,
                _ => return Err(anyhow!("Failed to convert sk_prf from base field to scalar field")),
            }
        };

        Ok(ComputeKey::new(pk_sig, sk_prf)?)
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

        Ok(Self::from(FromBytes::read_le(&data[9..41])?))
    }
}

impl<C: Parameters> fmt::Display for PrivateKey<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut private_key = [0u8; 41];
        private_key[0..9].copy_from_slice(&account_format::PRIVATE_KEY_PREFIX);

        self.sk_sig
            .write_le(&mut private_key[9..41])
            .expect("sk_sig formatting failed");

        write!(f, "{}", private_key.to_base58())
    }
}

impl<C: Parameters> fmt::Debug for PrivateKey<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "PrivateKey {{ sk_sig: {:?} }}", self.sk_sig)
    }
}
