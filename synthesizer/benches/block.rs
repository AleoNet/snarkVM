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

use console::{network::Testnet3, prelude::*};
use snarkvm_synthesizer::Block;

use criterion::Criterion;
use serde::{de::DeserializeOwned, Serialize};

type CurrentNetwork = Testnet3;

/// Loads the genesis block.
fn load_genesis_block() -> Block<CurrentNetwork> {
    Block::<CurrentNetwork>::from_bytes_le(CurrentNetwork::genesis_bytes()).unwrap()
}

/// Helper method to benchmark serialization.
fn bench_serialization<T: Serialize + DeserializeOwned + ToBytes + FromBytes + Clone>(
    c: &mut Criterion,
    name: &str,
    object: T,
) {
    ///////////////
    // Serialize //
    ///////////////

    // snarkvm_utilities::ToBytes
    {
        let object = object.clone();
        c.bench_function(&format!("{}::to_bytes_le", name), move |b| b.iter(|| object.to_bytes_le().unwrap()));
    }
    // bincode::serialize
    {
        let object = object.clone();
        c.bench_function(&format!("{}::serialize (bincode)", name), move |b| {
            b.iter(|| bincode::serialize(&object).unwrap())
        });
    }
    // serde_json::to_string
    {
        let object = object.clone();
        c.bench_function(&format!("{}::to_string (serde_json)", name), move |b| {
            b.iter(|| serde_json::to_string(&object).unwrap())
        });
    }

    /////////////////
    // Deserialize //
    /////////////////

    // snarkvm_utilities::FromBytes
    {
        let buffer = object.to_bytes_le().unwrap();
        c.bench_function(&format!("{}::from_bytes_le", name), move |b| b.iter(|| T::from_bytes_le(&buffer).unwrap()));
    }
    // bincode::deserialize
    {
        let buffer = bincode::serialize(&object).unwrap();
        c.bench_function(&format!("{}::deserialize (bincode)", name), move |b| {
            b.iter(|| bincode::deserialize::<T>(&buffer).unwrap())
        });
    }
    // serde_json::from_str
    {
        let object = serde_json::to_string(&object).unwrap();
        c.bench_function(&format!("{}::from_str (serde_json)", name), move |b| {
            b.iter(|| serde_json::from_str::<T>(&object).unwrap())
        });
    }
}

fn block_serialization(c: &mut Criterion) {
    let block = load_genesis_block();
    bench_serialization(c, "Block", block);
}

fn block_header_serialization(c: &mut Criterion) {
    let header = *load_genesis_block().header();
    bench_serialization(c, "Header", header);
}

fn block_transactions_serialization(c: &mut Criterion) {
    let transactions = load_genesis_block().transactions().clone();
    bench_serialization(c, "Transactions", transactions);
}

fn transaction_serialization(c: &mut Criterion) {
    let transaction = load_genesis_block().transactions().iter().next().unwrap().clone();
    bench_serialization(c, "Transaction", transaction);
}

fn transition_serialization(c: &mut Criterion) {
    let transaction = load_genesis_block().transactions().iter().next().unwrap().clone();
    let transition = transaction.transitions().next().unwrap().clone();
    bench_serialization(c, "Transition", transition);
}

criterion_group! {
    name = block;
    config = Criterion::default().sample_size(10);
    targets = block_serialization, block_header_serialization, block_transactions_serialization, transaction_serialization, transition_serialization
}

criterion_main!(block);
