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
mod string;
mod try_from;

use snarkvm_console_network::Network;
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{
    error,
    io::{Read, Result as IoResult, Write},
    CryptoRng,
    FromBytes,
    FromBytesDeserializer,
    Rng,
    ToBytes,
    ToBytesSerializer,
    UniformRand,
};

use anyhow::{anyhow, bail, Error, Result};
use base58::{FromBase58, ToBase58};
use core::{fmt, str::FromStr};
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct PrivateKey<N: Network> {
    /// The account seed that derives the full private key.
    seed: N::Scalar,
    /// The derived signature secret key.
    sk_sig: N::Scalar,
    /// The derived signature randomizer.
    r_sig: N::Scalar,
}

impl<N: Network> PrivateKey<N> {
    /// Samples a new random private key.
    #[inline]
    pub fn new<R: Rng + CryptoRng>(rng: &mut R) -> Result<Self> {
        // Sample a random account seed.
        Self::try_from(UniformRand::rand(rng))
    }

    /// Returns the account seed.
    pub const fn seed(&self) -> N::Scalar {
        self.seed
    }

    /// Returns the signature secret key.
    pub const fn sk_sig(&self) -> N::Scalar {
        self.sk_sig
    }

    /// Returns the signature randomizer.
    pub const fn r_sig(&self) -> N::Scalar {
        self.r_sig
    }
}
