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
    account::{Address, Field, PrivateKey},
    collections::U64,
    network::MainnetV0,
    program::{Identifier, Literal, Plaintext, ProgramID, Value},
};
use ledger_committee::{MAX_DELEGATORS, MIN_DELEGATOR_STAKE};
#[cfg(not(feature = "rocks"))]
use ledger_store::helpers::memory::ConsensusMemory;
#[cfg(feature = "rocks")]
use ledger_store::helpers::rocksdb::ConsensusDB;
use ledger_store::ConsensusStore;
use snarkvm_synthesizer::VM;

use criterion::Criterion;
use indexmap::indexmap;
use rayon::iter::{IntoParallelIterator, ParallelIterator};
use std::{str::FromStr, time::Duration};

pub type CurrentNetwork = MainnetV0;
#[cfg(feature = "rocks")]
pub type CurrentStorage = ConsensusDB<CurrentNetwork>;
#[cfg(not(feature = "rocks"))]
pub type CurrentStorage = ConsensusMemory<CurrentNetwork>;

fn bench_bonded_mappings(c: &mut Criterion) {
    // Construct the credits.aleo program ID.
    let credits_program_id = ProgramID::from_str("credits.aleo").unwrap();
    // Construct the bonded mapping name.
    let bonded_mapping = Identifier::from_str("bonded").unwrap();
    // Construct the bonded_state struct identifiers.
    let validator_identifier = Identifier::from_str("validator").expect("Failed to parse 'validator'");
    let microcredits_identifier = Identifier::from_str("microcredits").expect("Failed to parse 'microcredits'");
    // Create a DB store for the consensus.
    let store = ConsensusStore::<CurrentNetwork, CurrentStorage>::open(None).unwrap();
    // Create a VM from the store.
    let vm = VM::from(store).unwrap();
    // Get a sample validator address.
    let validator_address =
        Address::from_str("aleo1rhgdu77hgyqd3xjj8ucu3jj9r2krwz6mnzyd80gncr5fxcwlh5rsvzp9px").unwrap();

    // Generate 100_000 bonded mapping entries.
    let bonded_map = (0..(MAX_DELEGATORS as u64))
        .into_par_iter()
        .map(|i| {
            // Generate addresses for the stakers.
            let private_key = PrivateKey::try_from(Field::from_u64(i)).unwrap();
            let staker_address = Address::<CurrentNetwork>::try_from(&private_key).unwrap();

            // Create the bonded state.
            let bonded_state = indexmap! {
                validator_identifier => Plaintext::from(Literal::Address(validator_address)),
                microcredits_identifier => Plaintext::from(Literal::U64(U64::new(MIN_DELEGATOR_STAKE))),
            };
            (
                Plaintext::from(Literal::Address(staker_address)),
                Value::Plaintext(Plaintext::Struct(bonded_state, Default::default())),
            )
        })
        .collect::<Vec<(Plaintext<CurrentNetwork>, Value<CurrentNetwork>)>>();

    // Insert 100_000 entries into the bonded mapping.
    vm.finalize_store().replace_mapping(credits_program_id, bonded_mapping, bonded_map).unwrap();

    // Get a key to access the bonded mapping with.
    let private_key = PrivateKey::try_from(Field::from_u64(0)).unwrap();
    let staker_address = Address::<CurrentNetwork>::try_from(&private_key).unwrap();
    let key = Plaintext::from(Literal::Address(staker_address));

    // Benchmark get_value_speculative on the bonded mapping at 100_000 entries.
    c.bench_function("bonded mapping - get_value_speculative - 100_000 entries", |b| {
        b.iter(|| {
            let _value = vm.finalize_store().get_value_speculative(credits_program_id, bonded_mapping, &key).unwrap();
        })
    });

    // Benchmark get_value_confirmed on the bonded mapping at 100_000 entries.
    c.bench_function("bonded mapping - get_value_confirmed - 100_000 entries", |b| {
        b.iter(|| {
            let _value = vm.finalize_store().get_value_confirmed(credits_program_id, bonded_mapping, &key).unwrap();
        })
    });
}

criterion_group! {
    name = mappings;
    config = Criterion::default().sample_size(100).measurement_time(Duration::from_secs(10));
    targets = bench_bonded_mappings
}
criterion_main!(mappings);
