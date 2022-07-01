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

mod sign;
mod verify;

use snarkvm_console_account::{Address, ComputeKey};
use snarkvm_console_network::Network;
use snarkvm_console_types::prelude::*;

#[derive(Clone)]
pub struct SerialNumbers<N: Network> {
    /// The serial numbers of the record.
    serial_numbers: Vec<Field<N>>,
    /// The signature for the serial number: `(challenge, response, compute_key, gamma)`.
    signature: (Scalar<N>, Scalar<N>, ComputeKey<N>, Vec<Group<N>>),
}

impl<N: Network> From<(Vec<Field<N>>, (Scalar<N>, Scalar<N>, ComputeKey<N>, Vec<Group<N>>))> for SerialNumbers<N> {
    /// Note: See `SerialNumber::prove` to create a serial number. This method is used to eject from a circuit.
    fn from(
        (serial_numbers, (challenge, response, compute_key, gammas)): (
            Vec<Field<N>>,
            (Scalar<N>, Scalar<N>, ComputeKey<N>, Vec<Group<N>>),
        ),
    ) -> Self {
        Self { serial_numbers, signature: (challenge, response, compute_key, gammas) }
    }
}

impl<N: Network> SerialNumbers<N> {
    /// Returns the serial numbers.
    pub fn value(&self) -> &[Field<N>] {
        &self.serial_numbers
    }

    /// Returns the signature for the serial numbers.
    pub const fn signature(&self) -> &(Scalar<N>, Scalar<N>, ComputeKey<N>, Vec<Group<N>>) {
        &self.signature
    }
}
