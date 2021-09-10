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
use snarkvm_algorithms::{
    prf::Blake2s,
    traits::{CommitmentScheme, SignatureScheme, PRF},
};
use snarkvm_utilities::{FromBytes, ToBytes};

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
    pub seed: [u8; 32],
    pub r_pk_counter: u16,
    // Derived private attributes from the seed.
    sk_sig: <C::AccountSignatureScheme as SignatureScheme>::PrivateKey,
    compute_key: ComputeKey<C>,
}

impl<C: Parameters> PrivateKey<C> {
    const INITIAL_R_PK_COUNTER: u16 = 2;
    const INPUT_SK_PRF: [u8; 32] = [
        0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    ];
    const INPUT_SK_SIG: [u8; 32] = [0u8; 32];

    /// Creates a new account private key.
    pub fn new<R: Rng + CryptoRng>(rng: &mut R) -> Self {
        // Sample randomly until a valid private key is found.
        loop {
            // Samples a random account private key seed.
            let seed: [u8; 32] = rng.gen();

            // Returns the private key if it is valid.
            if let Ok(private_key) = Self::from_seed(&seed) {
                return private_key;
            }
        }
    }

    /// Derives the account private key from a given seed and verifies it is well-formed.
    pub fn from_seed(seed: &[u8; 32]) -> Result<Self, AccountError> {
        // Generate the signature private key.
        let sk_sig: <C::AccountSignatureScheme as SignatureScheme>::PrivateKey =
            FromBytes::read_le(Blake2s::evaluate(&seed, &Self::INPUT_SK_SIG)?.as_ref())?;

        // Derive the signature public key.
        let pk_sig = C::account_signature_scheme().generate_public_key(&sk_sig)?;

        // Generate the PRF secret key.
        let sk_prf: <C::SerialNumberPRF as PRF>::Seed =
            FromBytes::read_le(Blake2s::evaluate(&seed, &Self::INPUT_SK_PRF)?.as_ref())?;

        // Initialize a candidate compute key.
        let mut compute_key = ComputeKey::new(pk_sig, sk_prf, Default::default())?;

        // Derive the private key by iterating on the r_pk counter, until a valid r_pk is found.
        for r_pk_counter in Self::INITIAL_R_PK_COUNTER..u16::MAX {
            if let Ok(r_pk) = Self::derive_r_pk(seed, r_pk_counter) {
                // Update the candidate compute key with the derived value.
                compute_key.r_pk = r_pk;

                // Returns the private key if its compute key is valid.
                if compute_key.is_valid() {
                    return Ok(Self {
                        seed: *seed,
                        r_pk_counter,
                        sk_sig,
                        compute_key,
                    });
                }
            }
        }

        Err(AccountError::InvalidPrivateKeySeed)
    }

    /// Derives the account private key from a given seed and counter without verifying if it is well-formed.
    fn from_seed_and_counter(seed: &[u8; 32], r_pk_counter: u16) -> Result<Self, AccountError> {
        // Generate the signature private key.
        let sk_sig: <C::AccountSignatureScheme as SignatureScheme>::PrivateKey =
            FromBytes::read_le(Blake2s::evaluate(&seed, &Self::INPUT_SK_SIG)?.as_ref())?;

        // Derive the signature public key.
        let pk_sig = C::account_signature_scheme().generate_public_key(&sk_sig)?;

        // Generate the PRF secret key.
        let sk_prf: <C::SerialNumberPRF as PRF>::Seed =
            FromBytes::read_le(Blake2s::evaluate(&seed, &Self::INPUT_SK_PRF)?.as_ref())?;

        // Generate the randomness rpk for the commitment scheme.
        let r_pk = Self::derive_r_pk(seed, r_pk_counter)?;

        // Initialize a candidate compute key.
        let compute_key = ComputeKey::new(pk_sig, sk_prf, r_pk)?;

        // Construct the candidate private key.
        let private_key = Self {
            seed: *seed,
            r_pk_counter,
            sk_sig,
            compute_key,
        };

        // Returns the private key if it is valid.
        match private_key.is_valid() {
            true => Ok(private_key),
            false => Err(AccountError::InvalidPrivateKey),
        }
    }

    /// Returns `true` if the private key is well-formed. Otherwise, returns `false`.
    pub fn is_valid(&self) -> bool {
        self.r_pk_counter >= Self::INITIAL_R_PK_COUNTER && self.compute_key.is_valid()
    }

    /// Returns a reference to the signature private key.
    pub fn sk_sig(&self) -> &<C::AccountSignatureScheme as SignatureScheme>::PrivateKey {
        &self.sk_sig
    }

    /// Returns a reference to the compute key.
    pub fn compute_key(&self) -> &ComputeKey<C> {
        &self.compute_key
    }

    /// Generate the randomness r_pk for the commitment scheme from a given seed and counter.
    fn derive_r_pk(
        seed: &[u8; 32],
        counter: u16,
    ) -> Result<<C::AccountCommitmentScheme as CommitmentScheme>::Randomness, AccountError> {
        let mut r_pk_input = [0u8; 32];
        r_pk_input[0..2].copy_from_slice(&counter.to_le_bytes());

        // Generate the randomness r_pk for the commitment scheme.
        Ok(FromBytes::read_le(Blake2s::evaluate(seed, &r_pk_input)?.as_ref())?)
    }
}

impl<C: Parameters> FromStr for PrivateKey<C> {
    type Err = AccountError;

    /// Reads in an account private key string.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let data = s.from_base58()?;
        if data.len() != 43 {
            return Err(AccountError::InvalidByteLength(data.len()));
        }

        if data[0..9] != account_format::PRIVATE_KEY_PREFIX {
            return Err(AccountError::InvalidPrefixBytes(data[0..9].to_vec()));
        }

        let mut reader = &data[9..];
        let counter_bytes: [u8; 2] = FromBytes::read_le(&mut reader)?;
        let seed: [u8; 32] = FromBytes::read_le(&mut reader)?;

        Self::from_seed_and_counter(&seed, u16::from_le_bytes(counter_bytes))
    }
}

impl<C: Parameters> fmt::Display for PrivateKey<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut private_key = [0u8; 43];
        let prefix = account_format::PRIVATE_KEY_PREFIX;

        private_key[0..9].copy_from_slice(&prefix);
        private_key[9..11].copy_from_slice(&self.r_pk_counter.to_le_bytes());

        self.seed
            .write_le(&mut private_key[11..43])
            .expect("seed formatting failed");

        write!(f, "{}", private_key.to_base58())
    }
}

impl<C: Parameters> fmt::Debug for PrivateKey<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "PrivateKey {{ seed: {:?}, r_pk_counter: {:?} }}",
            self.seed, self.r_pk_counter
        )
    }
}
