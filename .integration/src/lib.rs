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

    let noop_program = NoopProgram::setup(rng)?;
    let noop_program_execution = noop_program.execute_blank_noop()?;

    let inner_circuit = InnerCircuit::<C>::blank();
    let inner_snark_parameters = C::InnerSNARK::setup(&inner_circuit, &mut SRS::CircuitSpecific(rng))?;

    let inner_snark_vk = inner_snark_parameters.1.clone();
    let inner_snark_proof = C::InnerSNARK::prove(&inner_snark_parameters.0, &inner_circuit, rng)?;
    let outer_snark_parameters = C::OuterSNARK::setup(
        &OuterCircuit::<C>::blank(inner_snark_vk, inner_snark_proof, noop_program_execution),
        &mut SRS::CircuitSpecific(rng),
    )?;

    Ok(DPC::<C> {
        noop_program,
        inner_proving_key: Some(inner_snark_parameters.0),
        inner_verifying_key: inner_snark_parameters.1,
        outer_proving_key: Some(outer_snark_parameters.0),
        outer_verifying_key: outer_snark_parameters.1,
    })
}

pub fn setup_or_load_dpc<C: Parameters, R: Rng + CryptoRng>(
    verify_only: bool,
    rng: &mut R,
) -> Result<DPC<C>, DPCError> {
    match DPC::<C>::load(verify_only) {
        Ok(dpc) => Ok(dpc),
        Err(err) => {
            println!("error - {}", err);
            setup_dpc(rng)
        }
    }
}
