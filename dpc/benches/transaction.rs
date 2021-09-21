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

#[macro_use]
extern crate criterion;

use snarkvm_dpc::{prelude::*, testnet1::*, testnet2::*};

use criterion::Criterion;
use rand::thread_rng;

fn coinbase_transaction<N: Network>(recipient: Address<N>, value: u64) -> Result<Transaction<N>, DPCError> {
    let rng = &mut thread_rng();

    let amount = AleoAmount::from_bytes(value as i64);
    let state = StateTransition::new_coinbase(recipient, amount, rng)?;
    let authorization = DPC::<N>::authorize(&vec![], &state, rng)?;
    let transaction = DPC::<N>::execute(authorization, state.executables(), &LedgerProof::default(), rng)?;

    Ok(transaction)
}

fn testnet1_coinbase_transaction(c: &mut Criterion) {
    let recipient_account = Account::<Testnet1>::new(&mut thread_rng()).unwrap();

    c.bench_function("testnet1_coinbase_transaction", move |b| {
        b.iter(|| {
            let _transaction = coinbase_transaction::<Testnet1>(recipient_account.address, 100).unwrap();
        })
    });
}

fn testnet2_coinbase_transaction(c: &mut Criterion) {
    let recipient_account = Account::<Testnet2>::new(&mut thread_rng()).unwrap();

    c.bench_function("testnet2_coinbase_transaction", move |b| {
        b.iter(|| {
            let _transaction = coinbase_transaction::<Testnet2>(recipient_account.address, 100).unwrap();
        })
    });
}

criterion_group! {
    name = transaction;
    config = Criterion::default().sample_size(10);
    targets = testnet1_coinbase_transaction, testnet2_coinbase_transaction
}

criterion_main!(transaction);
