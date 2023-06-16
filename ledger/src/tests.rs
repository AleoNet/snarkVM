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

use crate::{
    test_helpers::{CurrentLedger, CurrentNetwork},
    RecordsFilter,
};
use console::{
    account::{PrivateKey, ViewKey},
    network::prelude::*,
    program::{Entry, Identifier, Literal, Plaintext, Value},
};
use synthesizer::{
    store::{helpers::memory::ConsensusMemory, ConsensusStore},
    vm::VM,
    Program,
};

#[test]
fn test_load() {
    let rng = &mut TestRng::default();

    // Sample the genesis private key.
    let private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
    // Initialize the store.
    let store = ConsensusStore::<_, ConsensusMemory<_>>::open(None).unwrap();
    // Create a genesis block.
    let genesis = VM::from(store).unwrap().genesis(&private_key, rng).unwrap();

    // Initialize the ledger with the genesis block.
    let ledger = CurrentLedger::load(genesis.clone(), None).unwrap();
    assert_eq!(ledger.latest_hash(), genesis.hash());
    assert_eq!(ledger.latest_height(), genesis.height());
    assert_eq!(ledger.latest_round(), genesis.round());
    assert_eq!(ledger.latest_block(), genesis);
}

#[test]
fn test_load_unchecked() {
    // Load the genesis block.
    let genesis = crate::test_helpers::sample_genesis_block();

    // Initialize the ledger without checks.
    let ledger = CurrentLedger::load_unchecked(genesis.clone(), None).unwrap();
    assert_eq!(ledger.latest_hash(), genesis.hash());
    assert_eq!(ledger.latest_height(), genesis.height());
    assert_eq!(ledger.latest_round(), genesis.round());
    assert_eq!(ledger.latest_block(), genesis);

    // Initialize the ledger with the genesis block.
    let ledger = CurrentLedger::load(genesis.clone(), None).unwrap();
    assert_eq!(ledger.latest_hash(), genesis.hash());
    assert_eq!(ledger.latest_height(), genesis.height());
    assert_eq!(ledger.latest_round(), genesis.round());
    assert_eq!(ledger.latest_block(), genesis);
}

#[test]
fn test_state_path() {
    let rng = &mut TestRng::default();

    // Initialize the ledger.
    let ledger = crate::test_helpers::sample_ledger(PrivateKey::<CurrentNetwork>::new(rng).unwrap(), rng);
    // Retrieve the genesis block.
    let block = ledger.get_block(0).unwrap();

    // Construct the state path.
    let commitments = block.transactions().commitments().collect::<Vec<_>>();
    let commitment = commitments[0];

    let _state_path = ledger.get_state_path_for_commitment(commitment).unwrap();
}

#[test]
fn test_insufficient_finalize_fees() {
    let rng = &mut TestRng::default();

    // Sample the genesis private key.
    let private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
    let view_key = ViewKey::try_from(&private_key).unwrap();

    // Initialize the ledger.
    let ledger = crate::test_helpers::sample_ledger(private_key, rng);

    // Deploy a test program to the ledger.
    let program = Program::<CurrentNetwork>::from_str(
        r"
program dummy.aleo;
function foo:
    input r0 as u8.private;
    finalize r0;
finalize foo:
    input r0 as u8.public;
    add r0 r0 into r1;",
    )
    .unwrap();

    // A helper function to find records.
    let find_records = || {
        let microcredits = Identifier::from_str("microcredits").unwrap();
        ledger
            .find_records(&view_key, RecordsFilter::SlowUnspent(private_key))
            .unwrap()
            .filter(|(_, record)| match record.data().get(&microcredits) {
                Some(Entry::Private(Plaintext::Literal(Literal::U64(amount), _))) => !amount.is_zero(),
                _ => false,
            })
            .collect::<indexmap::IndexMap<_, _>>()
    };

    // Fetch the unspent records.
    let records = find_records();
    // Prepare the additional fee.
    let credits = records.values().next().unwrap().clone();
    let additional_fee = (credits, 6466000);

    // Deploy.
    let transaction = ledger.vm.deploy(&private_key, &program, additional_fee, None, rng).unwrap();
    // Verify.
    assert!(ledger.vm().verify_transaction(&transaction, None));

    // Construct the next block.
    let block = ledger.prepare_advance_to_next_block(&private_key, vec![transaction], None, rng).unwrap();
    // Advance to the next block.
    ledger.advance_to_next_block(&block).unwrap();
    assert_eq!(ledger.latest_height(), 1);
    assert_eq!(ledger.latest_hash(), block.hash());

    // Execute the test program, without providing enough fees for finalize, and ensure that the ledger deems the transaction invalid.
    // Fetch the unspent records.
    let records = find_records();
    // Select a record to spend.
    let record = records.values().next().unwrap().clone();

    // Prepare the inputs.
    let inputs = [Value::<CurrentNetwork>::from_str("1u8").unwrap()].into_iter();

    // Execute.
    let transaction = ledger
        .vm
        .execute(&private_key, ("dummy.aleo", "foo"), inputs.clone(), Some((record.clone(), 1_000)), None, rng)
        .unwrap();
    // Verify.
    assert!(ledger.vm.verify_transaction(&transaction, None));
    // Ensure that the ledger deems the transaction invalid.
    assert!(ledger.check_transaction_basic(&transaction, None).is_err());

    // Execute with enough fees.
    let transaction = ledger
        .vm
        .execute(&private_key, ("dummy.aleo", "foo"), inputs, Some((record, 2_000_000_000)), None, rng)
        .unwrap();
    // Verify.
    assert!(ledger.vm.verify_transaction(&transaction, None));
    // Ensure that the ledger deems the transaction valid.
    assert!(ledger.check_transaction_basic(&transaction, None).is_ok());
}
