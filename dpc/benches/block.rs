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

use snarkvm_dpc::{prelude::*, testnet2::Testnet2};

use criterion::Criterion;
use snarkvm_utilities::{FromBytes, ToBytes};

fn block_from_bytes(c: &mut Criterion) {
    let block_bytes = Testnet2::genesis_block().to_bytes_le().unwrap();

    c.bench_function("block_from_bytes", move |b| {
        b.iter(|| Block::<Testnet2>::from_bytes_le(&block_bytes).unwrap())
    });
}

criterion_group! {
    name = block;
    config = Criterion::default().sample_size(50);
    targets = block_from_bytes
}

criterion_main!(block);
