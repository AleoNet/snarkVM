// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#[macro_use]
extern crate criterion;

use console::{
    network::{
        prelude::{TestRng, Uniform},
        Testnet3,
    },
    types::{Address},
};
use snarkvm_synthesizer::staking_rewards;

use criterion::Criterion;
use indexmap::IndexMap;
use ledger_committee::Committee;
use std::time::Duration;

type CurrentNetwork = Testnet3;

const NUM_DELEGATORS: [u64; 7] = [0, 1000, 10_000, 100_000, 1_000_000, 10_000_000, 100_000_000];

fn bench_staking_rewards(c: &mut Criterion) {
    let mut rng = TestRng::default();

    // Construct the committee.
    println!("Constructing the committee...");
    let validators = (0..200).map(|_| {
        let address = Address::rand(&mut rng);
        let balance: u64 = 1_000_000_000_000;
        let is_open: bool = true;
        (address, (balance, is_open))
    }).collect::<IndexMap<Address<CurrentNetwork>, (u64, bool)>>();
    let committee = Committee::new(1, validators.clone()).unwrap();

    // Initialize the stakers.
    println!("Initializing the stakers...");
    let mut stakers = validators.iter().map(|(address, (balance, _))| {
        (*address, (*address, *balance))
    }).collect::<IndexMap<Address<CurrentNetwork>, (Address<CurrentNetwork>, u64)>>();

    // Initialize a counter for the number of delegators.
    let mut total_delegators = 0;

    // For each desired number of delegators, benchmark the `staking_rewards` function.
    for num_delegators in NUM_DELEGATORS {
        // Add the additional stakers.
        println!("Adding {} additional delegators...", num_delegators - total_delegators);
        for i in total_delegators..num_delegators {
            let address = Address::rand(&mut rng);
            let balance: u64 = 10_000_000;
            let (validator, _) = validators.get_index((i % 200) as usize).unwrap();
            stakers.insert(address, (*validator, balance));
        }
        total_delegators = num_delegators;

        // Run one round of staking rewards.
        println!("Running one round of staking rewards...");
        staking_rewards::<CurrentNetwork>(&stakers, &committee, 1_000_000_000);

        // Bench the `staking_rewards` function.
        println!("Benching the `staking_rewards` function...");
        c.bench_function(&format!("staking_rewards with {total_delegators} delegators and {} validators", validators.len()), |b| {
            b.iter_with_large_drop(|| {
                let _ = staking_rewards::<CurrentNetwork>(&stakers, &committee, 1_000_000_000);
            })
        });
    }
}

criterion_group! {
    name = rewards;
    config = Criterion::default().sample_size(10).measurement_time(Duration::from_secs(10));
    targets = bench_staking_rewards
}
criterion_main!(rewards);
