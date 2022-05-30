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

mod prove;
mod verify;

use snarkvm_console_network::Network;
use snarkvm_curves::{AffineCurve, ProjectiveCurve};
use snarkvm_utilities::{CryptoRng, Rng, ToBits, UniformRand};

use anyhow::Result;

pub struct SerialNumber<N: Network> {
    /// The serial number from the VRF.
    serial_number: N::Field,
    /// The proof for the serial number: `(gamma, challenge, response)`.
    proof: (N::Affine, N::Scalar, N::Scalar),
}

impl<N: Network> SerialNumber<N> {
    /// Returns the serial number from the VRF.
    pub const fn value(&self) -> &N::Field {
        &self.serial_number
    }

    /// Returns the proof for the serial number.
    pub const fn proof(&self) -> &(N::Affine, N::Scalar, N::Scalar) {
        &self.proof
    }
}
