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

use snarkvm_algorithms::{SNARK, SRS};
use snarkvm_curves::bls12_377::{Bls12_377, Fr};
use snarkvm_dpc::testnet2::Testnet2;
use snarkvm_ledger::posw::{circuit::POSWCircuit, PoswMarlin};
use snarkvm_marlin::ahp::AHPForR1CS;
use snarkvm_utilities::FromBytes;

use criterion::{criterion_group, criterion_main, Criterion};
use rand::SeedableRng;
use rand_chacha::ChaChaRng;

fn marlin_posw(c: &mut Criterion) {
    let mut group = c.benchmark_group("Proof of Succinct Work: Marlin");
    group.sample_size(10);

    let rng = &mut ChaChaRng::seed_from_u64(1234567);

    // Construct an instance of PoSW.
    let posw = {
        let max_degree = AHPForR1CS::<Testnet2::InnerScalarField>::max_degree(10000, 10000, 100000).unwrap();
        let universal_srs = <Testnet2::PoswSNARK as SNARK>::universal_setup(&max_degree, rng).unwrap();
        PoswMarlin::setup::<ChaChaRng>(&mut SRS::<ChaChaRng, _>::Universal(&universal_srs)).unwrap()
    };

    // Construct an assigned circuit.
    let nonce = 1u32;
    let leaves = vec![[3u8; 32]; 4];
    let assigned_circuit = POSWCircuit::<Testnet2, 32>::new(nonce, &leaves).unwrap();

    let difficulty_target = 0xFFFF_FFFF_FFFF_FFFF_u64;

    group.bench_function("mine", |b| {
        b.iter(|| {
            let (_nonce, _proof) = posw
                .mine(assigned_circuit.hashed_leaves(), difficulty_target, rng, u32::MAX)
                .unwrap();
        });
    });

    let (nonce, proof) = posw
        .mine(assigned_circuit.hashed_leaves(), difficulty_target, rng, u32::MAX)
        .unwrap();

    group.bench_function("verify", |b| {
        b.iter(|| {
            let _ = posw.verify(nonce, &proof, assigned_circuit.root()).unwrap();
        });
    });
}

criterion_group! {
    name = posw;
    config = Criterion::default().sample_size(10);
    targets = marlin_posw
}

criterion_main!(posw);
