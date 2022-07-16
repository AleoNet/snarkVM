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

use crate::polycommit::sonic_pc;
use snarkvm_curves::PairingEngine;
use snarkvm_utilities::{
    error,
    io::{self, Read, Write},
    serialize::*,
    FromBytes,
    ToBytes,
};

/// A certificate for the verifying key.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Certificate<E: PairingEngine> {
    /// An evaluation proof from the polynomial commitment.
    pub pc_proof: sonic_pc::BatchLCProof<E>,
}

impl<E: PairingEngine> Certificate<E> {
    /// Construct a new certificate.
    pub fn new(pc_proof: sonic_pc::BatchLCProof<E>) -> Self {
        Self { pc_proof }
    }
}

impl<E: PairingEngine> ToBytes for Certificate<E> {
    fn write_le<W: Write>(&self, mut w: W) -> io::Result<()> {
        Self::serialize_compressed(self, &mut w).map_err(|_| error("Failed to serialize certificate"))
    }
}

impl<E: PairingEngine> FromBytes for Certificate<E> {
    fn read_le<R: Read>(mut r: R) -> io::Result<Self> {
        Self::deserialize_compressed(&mut r).map_err(|_| error("Failed to deserialize certificate"))
    }
}
