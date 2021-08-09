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

use crate::{account_format, traits::Parameters, AccountError};
use snarkvm_algorithms::{
    prf::Blake2s,
    traits::{CommitmentScheme, EncryptionScheme, SignatureScheme, PRF},
};
use snarkvm_utilities::{from_bytes_le_to_bits_le, to_bytes_le, FromBytes, ToBytes};

use base58::{FromBase58, ToBase58};
use rand::{thread_rng, CryptoRng, Rng};
use std::{fmt, str::FromStr};

#[derive(Derivative)]
#[derivative(
    Clone(bound = "C: Parameters"),
    PartialEq(bound = "C: Parameters"),
    Eq(bound = "C: Parameters")
)]
pub struct PrivateKey<C: Parameters> {
    pub seed: [u8; 32],
    // Derived private attributes from the seed.
    pub sk_sig: <C::AccountSignatureScheme as SignatureScheme>::PrivateKey,
    pub sk_prf: <C::PRF as PRF>::Seed,
    pub r_pk: <C::AccountCommitmentScheme as CommitmentScheme>::Randomness,
    pub r_pk_counter: u16,
    // TODO (howardwu): Move this into a `ProverKey` struct.
    pk_sig: C::AccountSignaturePublicKey,
    // TODO (howardwu): Move this into a `ProverKey` struct.
    commitment_input: Vec<u8>,
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
        // Generate the SIG key pair.
        let sk_sig: <C::AccountSignatureScheme as SignatureScheme>::PrivateKey =
            FromBytes::read_le(Blake2s::evaluate(&seed, &Self::INPUT_SK_SIG)?.as_ref())?;
        let pk_sig = C::account_signature_scheme().generate_public_key(&sk_sig)?;

        // Generate the PRF secret key.
        let sk_prf: <C::PRF as PRF>::Seed =
            FromBytes::read_le(Blake2s::evaluate(&seed, &Self::INPUT_SK_PRF)?.as_ref())?;

        // Construct the commitment input for the account address.
        let commitment_input = to_bytes_le![pk_sig, sk_prf]?;

        // Initialize a candidate private key.
        let mut private_key = Self {
            seed: *seed,
            sk_sig,
            sk_prf,
            r_pk: Default::default(),
            r_pk_counter: Self::INITIAL_R_PK_COUNTER,
            pk_sig,
            commitment_input,
        };

        // Derive the private key by iterating on the r_pk counter, until a valid r_pk is found.
        for r_pk_counter in Self::INITIAL_R_PK_COUNTER..u16::MAX {
            if let Ok(r_pk) = Self::derive_r_pk(seed, r_pk_counter) {
                // Update the candidate private key with the derived values.
                private_key.r_pk = r_pk;
                private_key.r_pk_counter = r_pk_counter;

                // Returns the private key if it is valid.
                if private_key.is_valid() {
                    return Ok(private_key);
                }
            }
        }

        Err(AccountError::InvalidPrivateKeySeed)
    }

    /// Returns `true` if the private key is well-formed. Otherwise, returns `false`.
    pub fn is_valid(&self) -> bool {
        self.to_decryption_key().is_ok()
    }

    /// Returns the decryption key for the account view key.
    pub fn to_decryption_key(
        &self,
    ) -> Result<<C::AccountEncryptionScheme as EncryptionScheme>::PrivateKey, AccountError> {
        // Compute the commitment, which is used as the decryption key.
        let commitment = C::account_commitment_scheme().commit(&self.commitment_input, &self.r_pk)?;
        let commitment_bytes = commitment.to_bytes_le()?;

        // Determine the number of MSB bits we must enforce are zero,
        // for the isomorphism from the base field to the scalar field.
        let enforce_zero_on_num_bits = {
            debug_assert!(C::AccountEncryptionScheme::private_key_size_in_bits() > 0);
            // We must enforce that the MSB bit of the scalar field is also set to 0.
            let capacity = C::AccountEncryptionScheme::private_key_size_in_bits() - 1;
            let commitment_num_bits = commitment_bytes.len() * 8;
            assert!(capacity < commitment_num_bits);

            commitment_num_bits - capacity
        };

        // This operation explicitly enforces that the unused MSB bits
        // for the scalar field representation are correctly set to 0.
        for msb_bit in from_bytes_le_to_bits_le(&commitment_bytes[..])
            .rev()
            .take(enforce_zero_on_num_bits)
        {
            // Pop the next MSB bit, and enforce it is zero.
            if msb_bit {
                return Err(AccountError::InvalidAccountCommitment);
            }
        }

        // This operation implicitly enforces that the unused MSB bits
        // for the scalar field representation are correctly set to 0.
        let decryption_key: <C::AccountEncryptionScheme as EncryptionScheme>::PrivateKey =
            FromBytes::read_le(&commitment_bytes[..])?;

        Ok(decryption_key)
    }

    /// Returns the signature public key for deriving the account view key.
    pub fn pk_sig(&self) -> &C::AccountSignaturePublicKey {
        &self.pk_sig
    }

    /// Derives the account private key from a given seed and counter without verifying if it is well-formed.
    fn from_seed_and_counter(seed: &[u8; 32], r_pk_counter: u16) -> Result<Self, AccountError> {
        // Generate the SIG key pair.
        let sk_sig: <C::AccountSignatureScheme as SignatureScheme>::PrivateKey =
            FromBytes::read_le(Blake2s::evaluate(&seed, &Self::INPUT_SK_SIG)?.as_ref())?;
        let pk_sig = C::account_signature_scheme().generate_public_key(&sk_sig)?;

        // Generate the PRF secret key.
        let sk_prf: <C::PRF as PRF>::Seed =
            FromBytes::read_le(Blake2s::evaluate(&seed, &Self::INPUT_SK_PRF)?.as_ref())?;

        // Generate the randomness rpk for the commitment scheme.
        let r_pk = Self::derive_r_pk(seed, r_pk_counter)?;

        // Construct the commitment input for the account address.
        let commitment_input = to_bytes_le![pk_sig, sk_prf]?;

        // Construct the candidate private key.
        let private_key = Self {
            seed: *seed,
            sk_sig,
            sk_prf,
            r_pk,
            r_pk_counter,
            pk_sig,
            commitment_input,
        };

        // Returns the private key if it is valid.
        match private_key.is_valid() {
            true => Ok(private_key),
            false => Err(AccountError::InvalidPrivateKey),
        }
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

impl<C: Parameters> Default for PrivateKey<C> {
    fn default() -> Self {
        Self::new(&mut thread_rng())
    }
}
