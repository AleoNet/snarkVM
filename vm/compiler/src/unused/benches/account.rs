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

use snarkvm_dpc::{prelude::*, testnet2::Testnet2};

use criterion::Criterion;
use rand::thread_rng;

fn account_private_key(c: &mut Criterion) {
    let rng = &mut thread_rng();

    c.bench_function("account_private_key", move |b| {
        b.iter(|| {
            let _private_key = PrivateKey::<Testnet2>::new(rng);
        })
    });
}

fn account_view_key(c: &mut Criterion) {
    let rng = &mut thread_rng();

    c.bench_function("account_view_key", move |b| {
        let private_key = PrivateKey::<Testnet2>::new(rng);

        b.iter(|| {
            let _view_key = ViewKey::from_private_key(&private_key);
        })
    });
}

fn account_address(c: &mut Criterion) {
    let rng = &mut thread_rng();

    c.bench_function("account_address", move |b| {
        let private_key = PrivateKey::<Testnet2>::new(rng);

        b.iter(|| {
            let _address = Address::from_private_key(&private_key);
        })
    });
}

criterion_group! {
    name = account;
    config = Criterion::default().sample_size(20);
    targets = account_private_key, account_view_key, account_address
}

criterion_main!(account);
