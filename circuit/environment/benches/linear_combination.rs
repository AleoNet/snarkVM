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

use snarkvm_circuit::prelude::*;

use criterion::Criterion;

fn add(c: &mut Criterion) {
    let one = <Circuit as Environment>::BaseField::one();
    let two = one + one;

    const ITERATIONS: u64 = 1000;

    c.bench_function("LinearCombination::add", move |b| {
        b.iter(|| {
            let mut candidate = <Circuit as Environment>::one();
            for _ in 0..ITERATIONS {
                candidate = &candidate + &LinearCombination::from(Circuit::new_variable(Mode::Public, two));
            }
        })
    });

    c.bench_function("LinearCombination::add_assign", move |b| {
        b.iter(|| {
            let mut candidate = <Circuit as Environment>::one();
            for _ in 0..ITERATIONS {
                candidate += LinearCombination::from(Circuit::new_variable(Mode::Public, two));
            }
        })
    });
}

fn to_value(c: &mut Criterion) {
    let one = snarkvm_console_types::Field::<<Circuit as Environment>::Network>::one();
    let two = one + one;

    let mut candidate = Field::<Circuit>::one();
    (0..500_000).for_each(|_| {
        candidate += Field::new(Mode::Constant, two);
        candidate += Field::new(Mode::Public, two);
        candidate += Field::new(Mode::Private, two);
    });

    c.bench_function("to_value", move |b| {
        b.iter(|| {
            let _value = candidate.eject_value();
        })
    });
}

fn debug(c: &mut Criterion) {
    let one = snarkvm_console_types::Field::<<Circuit as Environment>::Network>::one();
    let two = one + one;

    let mut candidate = Field::<Circuit>::one();
    (0..500_000).for_each(|_| {
        candidate += Field::new(Mode::Constant, two);
        candidate += Field::new(Mode::Public, two);
        candidate += Field::new(Mode::Private, two);
    });

    c.bench_function("debug", move |b| {
        b.iter(|| {
            let _value = format!("{:?}", LinearCombination::from(&candidate));
        })
    });
}

criterion_group! {
    name = linear_combination;
    config = Criterion::default().sample_size(10);
    targets = add, to_value, debug
}

criterion_main!(linear_combination);
