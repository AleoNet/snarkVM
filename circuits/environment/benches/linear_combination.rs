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

use snarkvm_circuits::prelude::*;

use criterion::Criterion;

fn eject_value(c: &mut Criterion) {
    let one = <Circuit as Environment>::BaseField::one();
    let two = one + one;

    let mut candidate = Field::<Circuit>::one();
    (0..1_000_000).for_each(|_| {
        candidate += Field::new(Mode::Constant, two);
        candidate += Field::new(Mode::Public, two);
        candidate += Field::new(Mode::Private, two);
    });

    c.bench_function("eject_value", move |b| {
        b.iter(|| {
            let _value = candidate.eject_value();
        })
    });
}

criterion_group! {
    name = linear_combination;
    config = Criterion::default().sample_size(20);
    targets = eject_value
}

criterion_main!(linear_combination);
