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

use crate::aleo::{Network, PrivateKey};
use snarkvm_curves::{AffineCurve, ProjectiveCurve};
use snarkvm_utilities::{
    error,
    io::{Read, Result as IoResult, Write},
    FromBytes,
    ToBytes,
};

use anyhow::{Error, Result};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct ComputeKey<N: Network> {
    /// The signature public key `pk_sig` := G^sk_sig.
    pk_sig: N::Affine,
    /// The signature public randomizer `pr_sig` := G^r_sig.
    pr_sig: N::Affine,
    /// The VRF public key `pk_vrf` := G^sk_vrf.
    pk_vrf: N::Affine,
    /// The PRF secret key `sk_prf` := HashToScalar(pk_sig || pr_sig || pk_vrf).
    sk_prf: N::Scalar,
}

impl<N: Network> TryFrom<PrivateKey<N>> for ComputeKey<N> {
    type Error = Error;

    /// Derives the account compute key from an account private key.
    fn try_from(private_key: PrivateKey<N>) -> Result<Self, Self::Error> {
        Self::try_from(&private_key)
    }
}

impl<N: Network> TryFrom<&PrivateKey<N>> for ComputeKey<N> {
    type Error = Error;

    /// Derives the account compute key from an account private key.
    fn try_from(private_key: &PrivateKey<N>) -> Result<Self, Self::Error> {
        // Compute pk_sig := G^sk_sig.
        let pk_sig = N::g_scalar_multiply(&private_key.sk_sig());
        // Compute pr_sig := G^r_sig.
        let pr_sig = N::g_scalar_multiply(&private_key.r_sig());
        // Compute pk_vrf := G^sk_vrf.
        let pk_vrf = N::g_scalar_multiply(&private_key.sk_vrf());

        // Convert (pk_sig, pr_sig, pk_vrf) into affine coordinates.
        let (pk_sig, pr_sig, pk_vrf) = {
            let mut to_normalize = [pk_sig, pr_sig, pk_vrf];
            <N::Affine as AffineCurve>::Projective::batch_normalization(&mut to_normalize);
            let [pk_sig, pr_sig, pk_vrf] = to_normalize.map(|c| c.to_affine());
            (pk_sig, pr_sig, pk_vrf)
        };

        // Output the compute key.
        Self::new(pk_sig, pr_sig, pk_vrf)
    }
}

impl<N: Network> ComputeKey<N> {
    /// Initializes a new account compute key.
    ///
    /// This constructor is currently limited for internal use.
    /// The general convention for deriving a compute key should be from a private key.
    pub(crate) fn new(pk_sig: N::Affine, pr_sig: N::Affine, pk_vrf: N::Affine) -> Result<Self> {
        // Compute sk_prf := HashToScalar(pk_sig || pr_sig || pk_vrf).
        let sk_prf =
            N::hash_to_scalar_psd4(&[pk_sig.to_x_coordinate(), pr_sig.to_x_coordinate(), pk_vrf.to_x_coordinate()])?;
        // Output the compute key.
        Ok(Self { pk_sig, pr_sig, pk_vrf, sk_prf })
    }

    /// Returns the signature public key.
    pub fn pk_sig(&self) -> &N::Affine {
        &self.pk_sig
    }

    /// Returns the signature public randomizer.
    pub fn pr_sig(&self) -> &N::Affine {
        &self.pr_sig
    }

    /// Returns the VRF public key.
    pub fn pk_vrf(&self) -> &N::Affine {
        &self.pk_vrf
    }

    /// Returns a reference to the PRF secret key.
    pub fn sk_prf(&self) -> &N::Scalar {
        &self.sk_prf
    }
}

impl<N: Network> FromBytes for ComputeKey<N> {
    /// Reads an account compute key from a buffer.
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let pk_sig = N::affine_from_x_coordinate(N::Field::read_le(&mut reader)?).map_err(|e| error(format!("{e}")))?;
        let pr_sig = N::affine_from_x_coordinate(N::Field::read_le(&mut reader)?).map_err(|e| error(format!("{e}")))?;
        let pk_vrf = N::affine_from_x_coordinate(N::Field::read_le(&mut reader)?).map_err(|e| error(format!("{e}")))?;
        Ok(Self::new(pk_sig, pr_sig, pk_vrf).map_err(|e| error(format!("{e}")))?)
    }
}

impl<N: Network> ToBytes for ComputeKey<N> {
    /// Writes an account compute key to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.pk_sig.to_x_coordinate().write_le(&mut writer)?;
        self.pr_sig.to_x_coordinate().write_le(&mut writer)?;
        self.pk_vrf.to_x_coordinate().write_le(&mut writer)
    }
}
