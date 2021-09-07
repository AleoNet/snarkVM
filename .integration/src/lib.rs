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

use snarkvm_algorithms::prelude::*;
use snarkvm_dpc::prelude::*;

use rand::{CryptoRng, Rng};

pub fn setup_dpc<C: Parameters, R: Rng + CryptoRng>(rng: &mut R) -> Result<DPC<C>, DPCError> {
    println!("Running DPC setup...");

    Ok(DPC::<C> {
        noop_program: NoopProgram::setup(rng)?,
    })
}

pub fn setup_or_load_dpc<C: Parameters, R: Rng + CryptoRng>(rng: &mut R) -> Result<DPC<C>, DPCError> {
    match DPC::<C>::load() {
        Ok(dpc) => Ok(dpc),
        Err(err) => {
            println!("error - {}", err);
            setup_dpc(rng)
        }
    }
}
