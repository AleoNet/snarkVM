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

use crate::{AccountError, Network, PrivateKey};
use snarkvm_algorithms::SignatureSchemeOperations;
use snarkvm_curves::{AffineCurve, ProjectiveCurve};
use snarkvm_utilities::{FromBytes, ToBytes};

use rand::thread_rng;
use std::{
    fmt,
    io::{Read, Result as IoResult, Write},
};

#[derive(Clone, PartialEq, Eq)]
pub struct ComputeKey<N: Network> {
    /// pk_sig := G^sk_sig.
    pk_sig: N::ProgramAffineCurve,
    /// pr_sig := G^r_sig.
    pr_sig: N::ProgramAffineCurve,
    /// sk_prf := RO(G^sk_sig || G^r_sig).
    sk_prf: N::ProgramScalarField,
}

impl<N: Network> ComputeKey<N> {
    /// Creates a new account compute key.
    ///
    /// This constructor is currently limited for internal use.
    /// The general convention for deriving a compute key should be from a private key.
    pub(crate) fn new(pk_sig: N::ProgramAffineCurve, pr_sig: N::ProgramAffineCurve) -> Self {
        // Compute sk_prf := RO(G^sk_sig || G^r_sig).
        let sk_prf =
            N::account_signature_scheme().hash_to_scalar_field(&[pk_sig.to_x_coordinate(), pr_sig.to_x_coordinate()]);

        // Initialize the compute key.
        Self { pk_sig, pr_sig, sk_prf }
    }

    /// Derives the account compute key from an account private key.
    pub fn from_private_key(private_key: &PrivateKey<N>) -> Self {
        // Compute G^sk_sig.
        let pk_sig = N::account_signature_scheme().g_scalar_multiply(&private_key.sk_sig);

        // Compute G^r_sig.
        let pr_sig = N::account_signature_scheme().g_scalar_multiply(&private_key.r_sig);

        let mut to_normalize = [pk_sig, pr_sig];
        <N::ProgramAffineCurve as AffineCurve>::Projective::batch_normalization(&mut to_normalize);
        let [pk_sig, pr_sig] = to_normalize.map(|c| c.to_affine());

        Self::new(pk_sig, pr_sig)
    }

    pub fn from_signature(signature: &N::AccountSignature) -> Result<Self, AccountError> {
        // Extract G^sk_sig.
        let pk_sig = N::AccountSignatureScheme::pk_sig(signature)?;

        // Extract G^r_sig.
        let pr_sig = N::AccountSignatureScheme::pr_sig(signature)?;

        Ok(Self::new(pk_sig, pr_sig))
    }

    /// Returns `true` if the compute key is well-formed. Otherwise, returns `false`.
    pub fn is_valid(&self) -> bool {
        // Compute sk_prf := RO(G^sk_sig || G^r_sig).
        let candidate_sk_prf = N::account_signature_scheme()
            .hash_to_scalar_field(&[self.pk_sig.to_x_coordinate(), self.pr_sig.to_x_coordinate()]);

        self.sk_prf == candidate_sk_prf
    }

    /// Returns a reference to the signature root public key.
    pub fn pk_sig(&self) -> &N::ProgramAffineCurve {
        &self.pk_sig
    }

    /// Returns a reference to the signature root randomizer.
    pub fn pr_sig(&self) -> &N::ProgramAffineCurve {
        &self.pr_sig
    }

    /// Returns a reference to the PRF secret key.
    pub fn sk_prf(&self) -> &N::ProgramScalarField {
        &self.sk_prf
    }

    /// Returns the encryption key.
    pub fn to_encryption_key(&self) -> N::ProgramAffineCurve {
        // Compute G^sk_prf.
        let pk_prf = N::account_signature_scheme().g_scalar_multiply(&self.sk_prf);

        (self.pk_sig.to_projective() + self.pr_sig.to_projective() + pk_prf).into()
    }
}

impl<N: Network> FromBytes for ComputeKey<N> {
    /// Reads in an account compute key buffer.
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let pk_sig = FromBytes::read_le(&mut reader)?;
        let pr_sig = FromBytes::read_le(&mut reader)?;
        Ok(Self::new(pk_sig, pr_sig))
    }
}

impl<N: Network> ToBytes for ComputeKey<N> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.pk_sig.write_le(&mut writer)?;
        self.pr_sig.write_le(&mut writer)
    }
}

impl<N: Network> fmt::Debug for ComputeKey<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ComputeKey {{ pk_sig: {:?}, pr_sig: {:?} }}", self.pk_sig, self.pr_sig)
    }
}

impl<N: Network> Default for ComputeKey<N> {
    fn default() -> Self {
        PrivateKey::new(&mut thread_rng()).to_compute_key()
    }
}
