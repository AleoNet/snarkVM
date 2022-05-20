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
mod sign;

use crate::{Address, ComputeKey, Network, PrivateKey};
use snarkvm_curves::{AffineCurve, ProjectiveCurve};
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{
    io::{Read, Result as IoResult, Write},
    FromBits,
    FromBytes,
    ToBytes,
};

use anyhow::{anyhow, Result};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Signature<N: Network> {
    /// The verifier challenge to check against.
    challenge: N::Scalar,
    /// The prover response to the challenge.
    response: N::Scalar,
    /// The compute key of the prover.
    compute_key: ComputeKey<N>,
}

impl<N: Network> Signature<N> {
    /// Returns the verifier challenge.
    pub const fn challenge(&self) -> N::Scalar {
        self.challenge
    }

    /// Returns the prover response.
    pub const fn response(&self) -> N::Scalar {
        self.response
    }

    /// Returns the compute key.
    pub const fn compute_key(&self) -> ComputeKey<N> {
        self.compute_key
    }
}
