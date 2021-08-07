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
    record: Record<C>,
}

impl<C: Parameters> Output<C> {
    /// TODO (howardwu): TEMPORARY - `noop: Arc<NoopProgram<C>>` will be removed when `DPC::setup` and `DPC::load` are refactored.
    pub fn new_noop<R: Rng + CryptoRng>(
        noop: Arc<NoopProgram<C>>,
        position: u8,
        joint_serial_numbers: Vec<u8>,
        rng: &mut R,
    ) -> Result<Self> {
        // Construct the noop executable.
        let executable = Executable::Noop(noop);

        // Sample a burner noop private key.
        let noop_private_key = PrivateKey::new(rng)?;
        let noop_address = noop_private_key.try_into()?;

        // Construct the noop output record.
        let record = Record::new_noop_output(executable.program(), noop_address, position, joint_serial_numbers, rng)?;

        Ok(Self { record, executable })
    }
}
