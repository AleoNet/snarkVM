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

use snarkvm_circuit_environment::*;
use snarkvm_circuit_types_boolean::Boolean;

use criterion::Criterion;

fn bench_and(c: &mut Criterion) {
    c.bench_function("Boolean::and", move |b| {
        let first = Boolean::<Circuit>::new(Mode::Public, true);
        let second = Boolean::new(Mode::Private, true);

        b.iter(|| {
            let _third = &first & &second;
        })
    });

    c.bench_function("Boolean::and_assign", move |b| {
        let mut first = Boolean::<Circuit>::new(Mode::Public, true);
        let second = Boolean::new(Mode::Private, true);

        b.iter(|| {
            first &= &second;
        })
    });
}

criterion_group! {
    name = and;
    config = Criterion::default().sample_size(10);
    targets = bench_and
}

criterion_main!(and);
