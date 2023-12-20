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
    prelude::{FromBytes, Network},
    program::{Identifier, Literal, Plaintext, ProgramID, Value},
    types::Address,
};
use ledger_block::{Block, Ratify};
use ledger_store::ConsensusStore;
use std::str::FromStr;
use synthesizer::{
    program::{FinalizeGlobalState, FinalizeStoreTrait},
    VM,
};

use criterion::{BatchSize, Criterion};
use std::time::Duration;

type CurrentNetwork = Testnet3;

#[cfg(not(feature = "rocks"))]
type ConsensusType<N> = ledger_store::helpers::memory::ConsensusMemory<N>;
#[cfg(feature = "rocks")]
type ConsensusType<N> = ledger_store::helpers::rocksdb::ConsensusDB<N>;

const NUM_DELEGATORS: [u64; 4] = [0, 1000, 10_000, 100_000];

fn bench_atomic_post_ratify(c: &mut Criterion) {
    let rng = &mut TestRng::default();

    // Initialize storage.
    println!("Initializing storage...");
    let storage = ConsensusStore::<CurrentNetwork, ConsensusType<CurrentNetwork>>::open(Some(0)).unwrap();

    // Initialize the VM.
    println!("Initializing the VM...");
    let vm = VM::<CurrentNetwork, _>::from(storage).unwrap();
    let genesis_block = &Block::read_le(Testnet3::genesis_bytes()).unwrap();
    vm.add_next_block(genesis_block).unwrap();

    // Construct the program ID.
    let program_id = ProgramID::from_str("credits.aleo").unwrap();
    // Construct the committee mapping name.
    let committee_mapping_id = Identifier::from_str("committee").unwrap();
    // Construct the bonded mapping name.
    let bonded_mapping_id = Identifier::from_str("bonded").unwrap();
    // Construct the account mapping name.
    let account_mapping_id = Identifier::from_str("account").unwrap();

    // Get the finalize store.
    let finalize_store = vm.finalize_store();

    // Retrieve the committee mapping from storage.
    let mut current_committee_map = finalize_store.get_mapping_speculative(program_id, committee_mapping_id).unwrap();
    // Retrieve the bonded mapping from storage.
    let mut current_bonded_map = finalize_store.get_mapping_speculative(program_id, bonded_mapping_id).unwrap();
    // Retrieve the account mapping from storage.
    let mut current_account_map = finalize_store.get_mapping_speculative(program_id, account_mapping_id).unwrap();

    // Add the validators directly to the storage.
    println!("Adding the validators to storage...");
    let mut validators = Vec::with_capacity(200);
    // Track the existing validators.
    for (validator, _) in &current_committee_map {
        let address = match validator {
            Plaintext::Literal(Literal::Address(address), _) => *address,
            _ => panic!("Expected address "),
        };
        validators.push(address);
    }

    // Initialize the remaining validators.
    for _ in validators.len()..200 {
        let address = Address::rand(rng);
        let bonded_balance = 1_000_000_000_000u64;
        let account_balance = 1_000_000_000_000u64;
        let is_open = true;

        let committee_state =
            Value::from_str(&format!("{{ microcredits: {bonded_balance}u64, is_open: {is_open} }}")).unwrap();
        let bond_state =
            Value::from_str(&format!("{{ validator: {address}, microcredits: {bonded_balance}u64 }}")).unwrap();
        let account_balance = Value::from_str(&format!("{account_balance}u64")).unwrap();

        validators.push(address);

        current_committee_map.push((Plaintext::from(Literal::Address(address)), committee_state));
        current_bonded_map.push((Plaintext::from(Literal::Address(address)), bond_state));
        current_account_map.push((Plaintext::from(Literal::Address(address)), account_balance));
    }

    // Update the storage with the new validators.
    finalize_store.replace_mapping(program_id, committee_mapping_id, current_committee_map).unwrap();
    finalize_store.replace_mapping(program_id, bonded_mapping_id, current_bonded_map).unwrap();
    finalize_store.replace_mapping(program_id, account_mapping_id, current_account_map).unwrap();

    // Initialize a counter for the number of delegators.
    let mut total_delegators = 0;
    let mut round = genesis_block.round() + 1;
    let mut height = genesis_block.height() + 1;

    // For each desired number of delegators, benchmark the `staking_rewards` function.
    for num_delegators in NUM_DELEGATORS {
        // Retrieve the bonded mapping from storage.
        let mut current_bonded_map = finalize_store.get_mapping_speculative(program_id, bonded_mapping_id).unwrap();
        // Retrieve the account mapping from storage.
        let mut current_account_map = finalize_store.get_mapping_speculative(program_id, account_mapping_id).unwrap();

        // Add the additional delegators.
        println!("Adding {} delegators to storage...", num_delegators - total_delegators);
        for i in total_delegators..num_delegators {
            let address = Address::rand(rng);
            let validator = validators[(i as usize) % validators.len()];
            let bonded_balance = 10_000_000u64;
            let account_balance = 10_000_000u64;

            let bond_state =
                Value::from_str(&format!("{{ validator: {validator}, microcredits: {bonded_balance}u64 }}")).unwrap();
            let account_balance = Value::from_str(&format!("{account_balance}u64")).unwrap();

            let old_committee_state = match finalize_store
                .get_value_speculative(program_id, committee_mapping_id, &Plaintext::from(Literal::Address(validator)))
                .unwrap()
            {
                Some(Value::Plaintext(Plaintext::Struct(members, _))) => members,
                _ => panic!("Expected committee state"),
            };
            let validator_microcredits =
                match old_committee_state.get(&Identifier::from_str("microcredits").unwrap()).unwrap() {
                    Plaintext::Literal(Literal::U64(microcredits), _) => **microcredits,
                    _ => panic!("Expected microcredits"),
                };
            let new_committee_state = Value::from_str(&format!(
                "{{ microcredits: {}u64, is_open: true }}",
                validator_microcredits + bonded_balance
            ))
            .unwrap();
            finalize_store
                .update_key_value(
                    program_id,
                    committee_mapping_id,
                    Plaintext::from(Literal::Address(validator)),
                    new_committee_state,
                )
                .unwrap();

            current_bonded_map.push((Plaintext::from(Literal::Address(address)), bond_state));
            current_account_map.push((Plaintext::from(Literal::Address(address)), account_balance));
        }
        total_delegators = num_delegators;

        // Update the storage with the new delegators.
        finalize_store.replace_mapping(program_id, bonded_mapping_id, current_bonded_map).unwrap();
        finalize_store.replace_mapping(program_id, account_mapping_id, current_account_map).unwrap();

        // Bench the `staking_rewards` function.
        println!("Benching `atomic_post_ratify`...");
        #[cfg(not(feature = "rocks"))]
        let header = "Memory";
        #[cfg(feature = "rocks")]
        let header = "DB";
        c.bench_function(
            &format!(
                "{header}: `atomic_post_ratify` with {total_delegators} delegators and {} validators",
                validators.len()
            ),
            |b| {
                b.iter_batched(
                    || {
                        // Initialize the finalize state.
                        let finalize_state = FinalizeGlobalState::new::<CurrentNetwork>(
                            round,
                            height,
                            genesis_block.cumulative_weight(),
                            genesis_block.cumulative_proof_target(),
                            genesis_block.hash(),
                        )
                        .unwrap();
                        // Increment the round and height.
                        round += 1;
                        height += 1;
                        // Return the finalize state.
                        finalize_state
                    },
                    |finalize_state| {
                        let _ = VM::<CurrentNetwork, ConsensusType<CurrentNetwork>>::atomic_post_ratify(
                            finalize_store,
                            finalize_state,
                            [Ratify::BlockReward(1_000_000_000)].iter(),
                            None,
                        )
                        .unwrap();
                    },
                    BatchSize::PerIteration,
                )
            },
        );
    }
}

criterion_group! {
    name = atomic_post_ratify;
    config = Criterion::default().sample_size(10).measurement_time(Duration::from_secs(10));
    targets = bench_atomic_post_ratify
}
criterion_main!(atomic_post_ratify);
