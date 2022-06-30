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

use snarkvm_console_network::prelude::*;
use snarkvm_console_types::{Field, Scalar};

use base58::{FromBase58, ToBase58};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct PrivateKey<N: Network> {
    /// The account seed that derives the full private key.
    seed: Field<N>,
    /// The derived signature secret key.
    sk_sig: Scalar<N>,
    /// The derived signature randomizer.
    r_sig: Scalar<N>,
}

impl<N: Network> PrivateKey<N> {
    /// Samples a new random private key.
    #[inline]
    pub fn new<R: Rng + CryptoRng>(rng: &mut R) -> Result<Self> {
        // Sample a random account seed.
        Self::try_from(Uniform::rand(rng))
    }

    /// Returns the account seed.
    pub const fn seed(&self) -> Field<N> {
        self.seed
    }

    /// Returns the signature secret key.
    pub const fn sk_sig(&self) -> Scalar<N> {
        self.sk_sig
    }

    /// Returns the signature randomizer.
    pub const fn r_sig(&self) -> Scalar<N> {
        self.r_sig
    }
}
