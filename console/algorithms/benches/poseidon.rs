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

#[macro_use]
extern crate criterion;

use snarkvm_console_algorithms::{Poseidon2, Poseidon4, Poseidon8};
use snarkvm_console_types::prelude::*;
use snarkvm_utilities::{TestRng, Uniform};

use criterion::Criterion;
type F = Field<Console>;

fn poseidon2(c: &mut Criterion) {
    let rng = &mut TestRng::default();
    let hash = Poseidon2::<Console>::setup("Poseidon2").unwrap();

    let input = [F::rand(rng), F::rand(rng), F::rand(rng), F::rand(rng)];
    c.bench_function("Poseidon2 Hash 4 -> 1", |b| b.iter(|| hash.hash(&input)));
    c.bench_function("Poseidon2 Hash 4 -> 2", |b| b.iter(|| hash.hash_many(&input, 2)));

    let input = [F::rand(rng); 10];
    c.bench_function("Poseidon2 Hash 10 -> 1", |b| b.iter(|| hash.hash(&input)));
    c.bench_function("Poseidon2 Hash 10 -> 4", |b| b.iter(|| hash.hash_many(&input, 4)));
    c.bench_function("Poseidon2 Hash 10 -> 8", |b| b.iter(|| hash.hash_many(&input, 8)));
}

fn poseidon4(c: &mut Criterion) {
    let rng = &mut TestRng::default();
    let hash = Poseidon4::<Console>::setup("Poseidon4").unwrap();

    let input = [F::rand(rng), F::rand(rng), F::rand(rng), F::rand(rng)];
    c.bench_function("Poseidon4 Hash 4 -> 1", |b| b.iter(|| hash.hash(&input)));
    c.bench_function("Poseidon4 Hash 4 -> 2", |b| b.iter(|| hash.hash_many(&input, 2)));

    let input = [F::rand(rng); 10];
    c.bench_function("Poseidon4 Hash 10 -> 1", |b| b.iter(|| hash.hash(&input)));
    c.bench_function("Poseidon4 Hash 10 -> 4", |b| b.iter(|| hash.hash_many(&input, 4)));
    c.bench_function("Poseidon4 Hash 10 -> 8", |b| b.iter(|| hash.hash_many(&input, 8)));
}

fn poseidon8(c: &mut Criterion) {
    let rng = &mut TestRng::default();
    let hash = Poseidon8::<Console>::setup("Poseidon8").unwrap();

    let input = [F::rand(rng), F::rand(rng), F::rand(rng), F::rand(rng)];
    c.bench_function("Poseidon8 Hash 4 -> 1", |b| b.iter(|| hash.hash(&input)));
    c.bench_function("Poseidon8 Hash 4 -> 2", |b| b.iter(|| hash.hash_many(&input, 2)));

    let input = [F::rand(rng); 10];
    c.bench_function("Poseidon8 Hash 10 -> 1", |b| b.iter(|| hash.hash(&input)));
    c.bench_function("Poseidon8 Hash 10 -> 4", |b| b.iter(|| hash.hash_many(&input, 4)));
    c.bench_function("Poseidon8 Hash 10 -> 8", |b| b.iter(|| hash.hash_many(&input, 8)));
}

criterion_group! {
    name = sponge;
    config = Criterion::default().sample_size(50);
    targets = poseidon2, poseidon4, poseidon8,
}

criterion_main!(sponge);
