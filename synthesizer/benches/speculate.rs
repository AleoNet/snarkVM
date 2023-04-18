// Copyright (C) 2019-2023 Aleo Systems Inc.
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

use criterion::Criterion;

mod utilities;
use utilities::*;

use console::{account::PrivateKey, network::Testnet3, prelude::Zero, types::Field};
use snarkvm_synthesizer::{Speculate, Transaction};

use snarkvm_utilities::{TestRng, ToBytes};

const NUM_MAPPINGS: &[usize] = &[0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65535];

fn speculate_deployment_transaction(c: &mut Criterion) {
    let rng = &mut TestRng::default();

    // Sample a new private key and address.
    let private_key = PrivateKey::<Testnet3>::new(rng).unwrap();

    // Initialize a `Namer` to help construct unique programs.
    let mut namer = Namer::new();

    // Create a new benchmark group.
    let mut group = c.benchmark_group("speculate_deployment_transaction");
    for num_mappings in NUM_MAPPINGS {
        // Initialize the VM.
        let (vm, record) = initialize_vm(&private_key, rng);

        // Construct a new program.
        let program =
            construct_program(ProgramConfig { num_mappings: *num_mappings, transition_configs: vec![] }, &mut namer);

        // Calculate the program size.
        let program_size = program.to_bytes_le().unwrap().len();

        // Construct a deployment transaction.
        let transaction =
            Transaction::deploy(&vm, &private_key, &program, (record.clone(), program_size as u64), None, rng).unwrap();

        // Construct a `Speculate` object.
        let mut speculate = Speculate::new(vm.program_store().current_storage_root());

        // Benchmark the speculation of a deployment with the given number of mappings.
        group.bench_function(&format!("speculate_deployment/{}_mappings/", num_mappings), |b| {
            b.iter(|| speculate.speculate_transaction(&vm, &transaction))
        });

        // Benchmark the commitment of a deployment with the given number of mappings.
        group.bench_function(&format!("commit_deployment/{}_mappings/", num_mappings), |b| {
            b.iter(|| speculate.commit(&vm));
        });
    }
    group.finish();
}

// fn speculate_execution(c: &mut Criterion) {
//     todo!()
// }

criterion_group! {
    name = speculate;
    config = Criterion::default().sample_size(10);
    targets = speculate_deployment_transaction
}

criterion_main!(speculate);
