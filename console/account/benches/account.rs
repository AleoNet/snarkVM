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

use snarkvm_console_account::{Address, PrivateKey, ViewKey};
use snarkvm_console_network::{environment::prelude::*, Testnet3};

use criterion::Criterion;

type CurrentNetwork = Testnet3;

fn account_private_key(c: &mut Criterion) {
    let rng = &mut TestRng::default();

    c.bench_function("account_private_key", move |b| {
        b.iter(|| {
            let _private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        })
    });
}

fn account_view_key(c: &mut Criterion) {
    let rng = &mut TestRng::default();

    c.bench_function("account_view_key", move |b| {
        let private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();

        b.iter(|| {
            let _view_key = ViewKey::try_from(&private_key).unwrap();
        })
    });
}

fn account_address(c: &mut Criterion) {
    let rng = &mut TestRng::default();

    c.bench_function("account_address", move |b| {
        let private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();

        b.iter(|| {
            let _address = Address::try_from(&private_key).unwrap();
        })
    });
}

criterion_group! {
    name = account;
    config = Criterion::default().sample_size(20);
    targets = account_private_key, account_view_key, account_address
}

criterion_main!(account);
