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

use snarkvm_console_algorithms::{BHP1024, BHP256, BHP512, BHP768};
use snarkvm_console_types::prelude::*;
use snarkvm_utilities::{TestRng, Uniform};

use criterion::Criterion;

fn bhp256(c: &mut Criterion) {
    let rng = &mut TestRng::default();
    let hash = BHP256::<Console>::setup("BHP256").unwrap();

    let input = (0..hash.window_size() as u64 * hash.num_windows() as u64).map(|_| bool::rand(rng)).collect::<Vec<_>>();
    c.bench_function(&format!("BHP256 Hash - input size {}", input.len()), |b| b.iter(|| hash.hash(&input)));

    let input = (0..256).map(|_| bool::rand(rng)).collect::<Vec<_>>();
    c.bench_function(&format!("BHP256 Hash - input size {}", input.len()), |b| b.iter(|| hash.hash(&input)));
}

fn bhp512(c: &mut Criterion) {
    let rng = &mut TestRng::default();
    let hash = BHP512::<Console>::setup("BHP512").unwrap();

    let input = (0..hash.window_size() as u64 * hash.num_windows() as u64).map(|_| bool::rand(rng)).collect::<Vec<_>>();
    c.bench_function(&format!("BHP512 Hash - input size {}", input.len()), |b| b.iter(|| hash.hash(&input)));

    let input = (0..512).map(|_| bool::rand(rng)).collect::<Vec<_>>();
    c.bench_function(&format!("BHP512 Hash - input size {}", input.len()), |b| b.iter(|| hash.hash(&input)));
}

fn bhp768(c: &mut Criterion) {
    let rng = &mut TestRng::default();
    let hash = BHP768::<Console>::setup("BHP768").unwrap();

    let input = (0..hash.window_size() as u64 * hash.num_windows() as u64).map(|_| bool::rand(rng)).collect::<Vec<_>>();
    c.bench_function(&format!("BHP768 Hash - input size {}", input.len()), |b| b.iter(|| hash.hash(&input)));

    let input = (0..768).map(|_| bool::rand(rng)).collect::<Vec<_>>();
    c.bench_function(&format!("BHP768 Hash - input size {}", input.len()), |b| b.iter(|| hash.hash(&input)));
}

fn bhp1024(c: &mut Criterion) {
    let rng = &mut TestRng::default();
    let hash = BHP1024::<Console>::setup("BHP1024").unwrap();

    let input = (0..hash.window_size() as u64 * hash.num_windows() as u64).map(|_| bool::rand(rng)).collect::<Vec<_>>();
    c.bench_function(&format!("BHP1024 Hash - input size {}", input.len()), |b| b.iter(|| hash.hash(&input)));

    let input = (0..1024).map(|_| bool::rand(rng)).collect::<Vec<_>>();
    c.bench_function(&format!("BHP1024 Hash - input size {}", input.len()), |b| b.iter(|| hash.hash(&input)));
}

criterion_group! {
    name = bhp;
    config = Criterion::default().sample_size(1000);
    targets = bhp256, bhp512, bhp768, bhp1024
}

criterion_main!(bhp);
