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

#[macro_use]
extern crate criterion;

use snarkvm_algorithms::traits::*;
use snarkvm_dpc::{prelude::*, testnet2::Testnet2};

use criterion::Criterion;
use rand::thread_rng;

fn noop_program_setup(c: &mut Criterion) {
    let rng = &mut thread_rng();

    c.bench_function("NoopProgram::setup", move |b| {
        b.iter(|| {
            // Compute the proving key and verifying key.
            let (_proving_key, verifying_key) = <<Testnet2 as Network>::ProgramSNARK as SNARK>::setup(
                &SynthesizedCircuit::<Testnet2>::Noop(Default::default()),
                &mut *Testnet2::program_srs(rng).borrow_mut(),
            )
            .unwrap();

            // Compute the circuit ID.
            let _circuit_id = <Testnet2 as Network>::program_circuit_id(&verifying_key).unwrap();
        })
    });
}

fn noop_program_load(c: &mut Criterion) {
    c.bench_function("NoopProgram::load", move |b| {
        b.iter(|| {
            let _noop_program = Testnet2::noop_program();
        })
    });
}

criterion_group! {
    name = noop_program;
    config = Criterion::default().sample_size(10);
    targets = noop_program_setup, noop_program_load
}

criterion_main!(noop_program);
