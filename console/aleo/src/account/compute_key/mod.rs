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

mod bytes;
mod serialize;
mod try_from;

use crate::PrivateKey;
use snarkvm_console_network::Network;
use snarkvm_curves::{AffineCurve, ProjectiveCurve};
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{
    error,
    io::{Read, Result as IoResult, Write},
    FromBytes,
    FromBytesDeserializer,
    ToBytes,
    ToBytesSerializer,
};

use anyhow::{Error, Result};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

static _COMPUTE_KEY_PREFIX: [u8; 10] = [109, 249, 98, 224, 36, 15, 213, 187, 79, 190]; // AComputeKey1

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

impl<N: Network> ComputeKey<N> {
    /// Returns the signature public key.
    pub const fn pk_sig(&self) -> N::Affine {
        self.pk_sig
    }

    /// Returns the signature public randomizer.
    pub const fn pr_sig(&self) -> N::Affine {
        self.pr_sig
    }

    /// Returns the VRF public key.
    pub const fn pk_vrf(&self) -> N::Affine {
        self.pk_vrf
    }

    /// Returns a reference to the PRF secret key.
    pub const fn sk_prf(&self) -> N::Scalar {
        self.sk_prf
    }
}
