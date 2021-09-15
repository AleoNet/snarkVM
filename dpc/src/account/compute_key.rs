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
use snarkvm_algorithms::SignatureSchemeOperations;
use snarkvm_curves::AffineCurve;
use snarkvm_utilities::{FromBytes, ToBytes};

use rand::thread_rng;
use std::{
    fmt,
    io::{Read, Result as IoResult, Write},
};

#[derive(Derivative)]
#[derivative(
    Clone(bound = "C: Parameters"),
    PartialEq(bound = "C: Parameters"),
    Eq(bound = "C: Parameters")
)]
pub struct ComputeKey<C: Parameters> {
    /// pk_sig := G^sk_sig.
    pk_sig: C::ProgramAffineCurve,
    /// pr_sig := G^r_sig.
    pr_sig: C::ProgramAffineCurve,
    /// sk_prf := RO(G^sk_sig || G^r_sig).
    sk_prf: C::ProgramScalarField,
}

impl<C: Parameters> ComputeKey<C> {
    /// Creates a new account compute key.
    ///
    /// This constructor is currently limited for internal use.
    /// The general convention for deriving a compute key should be from a private key.
    pub(crate) fn new(pk_sig: C::ProgramAffineCurve, pr_sig: C::ProgramAffineCurve) -> Result<Self, AccountError> {
        // Compute sk_prf := RO(G^sk_sig || G^r_sig).
        let sk_prf = C::account_signature_scheme()
            .hash_to_scalar_field(&[pk_sig.to_x_coordinate(), pr_sig.to_x_coordinate()])?;

        // Initialize the compute key.
        Ok(Self { pk_sig, pr_sig, sk_prf })
    }

    /// Derives the account compute key from an account private key.
    pub fn from_private_key(private_key: &PrivateKey<C>) -> Result<Self, AccountError> {
        // Compute G^sk_sig.
        let pk_sig = C::account_signature_scheme().g_scalar_multiply(&private_key.sk_sig)?;

        // Compute G^r_sig.
        let pr_sig = C::account_signature_scheme().g_scalar_multiply(&private_key.r_sig)?;

        Self::new(pk_sig, pr_sig)
    }

    pub fn from_signature(signature: &C::AccountSignature) -> Result<Self, AccountError> {
        // Extract G^sk_sig.
        let pk_sig = C::AccountSignatureScheme::pk_sig(signature)?;

        // Extract G^r_sig.
        let pr_sig = C::AccountSignatureScheme::pr_sig(signature)?;

        Self::new(pk_sig, pr_sig)
    }

    /// Returns `true` if the compute key is well-formed. Otherwise, returns `false`.
    pub fn is_valid(&self) -> bool {
        // Compute sk_prf := RO(G^sk_sig || G^r_sig).
        match C::account_signature_scheme()
            .hash_to_scalar_field(&[self.pk_sig.to_x_coordinate(), self.pr_sig.to_x_coordinate()])
        {
            Ok(candidate_sk_prf) => self.sk_prf == candidate_sk_prf,
            Err(error) => {
                eprintln!("Failed to validate compute key: {}", error);
                false
            }
        }
    }

    /// Returns a reference to the signature root public key.
    pub fn pk_sig(&self) -> &C::ProgramAffineCurve {
        &self.pk_sig
    }

    /// Returns a reference to the signature root randomizer.
    pub fn pr_sig(&self) -> &C::ProgramAffineCurve {
        &self.pr_sig
    }

    /// Returns a reference to the PRF secret key.
    pub fn sk_prf(&self) -> &C::ProgramScalarField {
        &self.sk_prf
    }

    /// Returns the encryption key.
    pub fn to_encryption_key(&self) -> Result<C::ProgramAffineCurve, AccountError> {
        // Compute G^sk_prf.
        let pk_prf = C::account_signature_scheme().g_scalar_multiply(&self.sk_prf)?;

        Ok(self.pk_sig + self.pr_sig + pk_prf)
    }
}

impl<C: Parameters> FromBytes for ComputeKey<C> {
    /// Reads in an account compute key buffer.
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let pk_sig = FromBytes::read_le(&mut reader)?;
        let pr_sig = FromBytes::read_le(&mut reader)?;
        Ok(Self::new(pk_sig, pr_sig)?)
    }
}

impl<C: Parameters> ToBytes for ComputeKey<C> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.pk_sig.write_le(&mut writer)?;
        self.pr_sig.write_le(&mut writer)
    }
}

impl<C: Parameters> fmt::Debug for ComputeKey<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "ComputeKey {{ pk_sig: {:?}, pr_sig: {:?} }}",
            self.pk_sig, self.pr_sig
        )
    }
}

impl<C: Parameters> Default for ComputeKey<C> {
    fn default() -> Self {
        PrivateKey::new(&mut thread_rng())
            .to_compute_key()
            .expect("Failed to generate a random compute key")
    }
}
