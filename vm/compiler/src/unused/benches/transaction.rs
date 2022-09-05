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

use snarkvm_dpc::{prelude::*, testnet1::*, testnet2::*};

use criterion::Criterion;
use rand::thread_rng;

fn testnet1_coinbase_transaction(c: &mut Criterion) {
    let rng = &mut thread_rng();

    let address = Account::<Testnet1>::new(rng).address();
    let amount = AleoAmount::from_aleo(100);

    c.bench_function("testnet1_coinbase_transaction", move |b| {
        b.iter(|| {
            let _transaction = Transaction::<Testnet1>::new_coinbase(address, amount, true, rng).unwrap();
        })
    });
}

fn testnet2_coinbase_transaction(c: &mut Criterion) {
    let rng = &mut thread_rng();

    let address = Account::<Testnet2>::new(rng).address();
    let amount = AleoAmount::from_aleo(100);

    c.bench_function("testnet2_coinbase_transaction", move |b| {
        b.iter(|| {
            let _transaction = Transaction::<Testnet2>::new_coinbase(address, amount, true, rng).unwrap();
        })
    });
}

criterion_group! {
    name = transaction;
    config = Criterion::default().sample_size(10);
    targets = testnet1_coinbase_transaction, testnet2_coinbase_transaction
}

criterion_main!(transaction);
