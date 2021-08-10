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

use crate::{AccountError, Parameters, PrivateKey};
use snarkvm_algorithms::{CommitmentScheme, EncryptionScheme, PRF};
use snarkvm_utilities::{from_bytes_le_to_bits_le, to_bytes_le, FromBytes, ToBits, ToBytes};

use rand::thread_rng;
use std::fmt;

#[derive(Derivative)]
#[derivative(
    Clone(bound = "C: Parameters"),
    PartialEq(bound = "C: Parameters"),
    Eq(bound = "C: Parameters")
)]
pub struct ComputeKey<C: Parameters> {
    pk_sig: C::AccountSignaturePublicKey,
    sk_prf: <C::PRF as PRF>::Seed,
    pub(super) r_pk: <C::AccountCommitmentScheme as CommitmentScheme>::Randomness,
    commitment_input: Vec<u8>,
}

impl<C: Parameters> ComputeKey<C> {
    /// Creates a new account compute key.
    ///
    /// This constructor is currently limited for internal use.
    /// The general convention for deriving a compute key should be from a private key.
    pub(crate) fn new(
        pk_sig: C::AccountSignaturePublicKey,
        sk_prf: <C::PRF as PRF>::Seed,
        r_pk: <C::AccountCommitmentScheme as CommitmentScheme>::Randomness,
    ) -> Result<Self, AccountError> {
        // Construct the commitment input for the account address.
        let commitment_input = to_bytes_le![pk_sig, sk_prf]?;

        // Initialize a candidate compute key.
        let compute_key = Self {
            pk_sig,
            sk_prf,
            r_pk,
            commitment_input,
        };

        // Returns the compute key if it is valid.
        match compute_key.is_valid() {
            true => Ok(compute_key),
            false => Err(AccountError::InvalidComputeKey),
        }
    }

    /// Returns `true` if the private key is well-formed. Otherwise, returns `false`.
    pub fn is_valid(&self) -> bool {
        self.to_decryption_key().is_ok()
    }

    /// Returns a reference to the signature public key.
    pub fn pk_sig(&self) -> &C::AccountSignaturePublicKey {
        &self.pk_sig
    }

    /// Returns a reference to the PRF secret key.
    pub fn sk_prf(&self) -> &<C::PRF as PRF>::Seed {
        &self.sk_prf
    }

    /// Returns a reference to the commitment randomness for the decryption key.
    pub fn r_pk(&self) -> &<C::AccountCommitmentScheme as CommitmentScheme>::Randomness {
        &self.r_pk
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

        // This operation enforces that the base field element fits within the scalar field.
        // However, this operation does not enforce that the MSB of the scalar field element is 0.
        let decryption_key: <C::AccountEncryptionScheme as EncryptionScheme>::PrivateKey =
            FromBytes::read_le(&commitment_bytes[..])?;

        // Enforce the MSB of the scalar field element is 0 by convention.
        debug_assert_eq!(Some(&false), decryption_key.to_bits_be().iter().next());

        Ok(decryption_key)
    }
}

impl<C: Parameters> fmt::Debug for ComputeKey<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "ComputeKey {{ pk_sig: {:?}, sk_prf: {:?}, r_pk: {:?} }}",
            self.pk_sig, self.sk_prf, self.r_pk
        )
    }
}

impl<C: Parameters> Default for ComputeKey<C> {
    fn default() -> Self {
        PrivateKey::new(&mut thread_rng()).compute_key().clone()
    }
}
