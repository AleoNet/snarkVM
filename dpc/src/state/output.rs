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

use crate::prelude::*;

use anyhow::Result;
use rand::{CryptoRng, Rng};
use std::{convert::TryInto, sync::Arc};

#[derive(Derivative)]
#[derivative(Clone(bound = "C: Parameters"))]
pub struct Output<C: Parameters> {
    executable: Executable<C>,
    address: Address<C>,
    value: AleoAmount,
    payload: Payload,
    is_dummy: bool,
}

impl<C: Parameters> Output<C> {
    /// TODO (howardwu): TEMPORARY - `noop: Arc<NoopProgram<C>>` will be removed when `DPC::setup` and `DPC::load` are refactored.
    pub fn new_noop<R: Rng + CryptoRng>(noop: Arc<NoopProgram<C>>, rng: &mut R) -> Result<Self> {
        // Construct the noop executable.
        let executable = Executable::Noop(noop);

        // Sample a burner noop private key.
        let noop_private_key = PrivateKey::new(rng);
        let noop_address = noop_private_key.try_into()?;

        Ok(Self {
            executable,
            address: noop_address,
            value: AleoAmount::from_bytes(0),
            payload: Payload::default(),
            is_dummy: true,
        })
    }

    /// TODO (howardwu): TEMPORARY - `noop: Arc<NoopProgram<C>>` will be removed when `DPC::setup` and `DPC::load` are refactored.
    /// Initializes a new instance of `Output`.
    pub fn new(
        address: Address<C>,
        value: AleoAmount,
        payload: Payload,
        executable: Option<Executable<C>>,
        noop: Arc<NoopProgram<C>>,
    ) -> Result<Self> {
        // Retrieve the executable. If `None` is provided, construct the noop executable.
        let executable = match executable {
            Some(executable) => executable,
            None => Executable::Noop(noop),
        };

        // Determine if the record is a dummy.
        let is_dummy = value == AleoAmount::from_bytes(0) && payload.is_empty() && executable.is_noop();

        Ok(Self {
            executable,
            address,
            value,
            payload,
            is_dummy,
        })
    }

    /// Returns the output record, given the position and joint serial numbers.
    pub fn to_record<R: Rng + CryptoRng>(
        &self,
        position: u8,
        joint_serial_numbers: &Vec<u8>,
        rng: &mut R,
    ) -> Result<Record<C>> {
        Ok(Record::new_output(
            self.executable.program(),
            self.address,
            self.is_dummy,
            self.value.0 as u64,
            self.payload.clone(),
            position,
            joint_serial_numbers,
            rng,
        )?)
    }
}
