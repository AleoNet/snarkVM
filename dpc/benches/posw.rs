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

use std::sync::atomic::AtomicBool;

use snarkvm_dpc::{testnet2::Testnet2, Network, PoSWScheme};

use criterion::{criterion_group, criterion_main, Criterion};
use rand::SeedableRng;
use rand_chacha::ChaChaRng;

fn marlin_posw(c: &mut Criterion) {
    let mut group = c.benchmark_group("Proof of Succinct Work: Marlin");
    group.sample_size(10);

    let rng = &mut ChaChaRng::seed_from_u64(1234567);

    // Construct a block header.
    let mut block_header = Testnet2::genesis_block().header().clone();

    group.bench_function("mine", |b| {
        b.iter(|| {
            Testnet2::posw()
                .mine(&mut block_header, &AtomicBool::new(false), rng)
                .unwrap();
        });
    });

    group.bench_function("verify", |b| {
        b.iter(|| {
            let _is_valid = Testnet2::posw().verify(&block_header);
        });
    });
}

criterion_group! {
    name = posw;
    config = Criterion::default().sample_size(10);
    targets = marlin_posw
}

criterion_main!(posw);
