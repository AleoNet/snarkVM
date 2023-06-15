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

use crate::{tests::test_helpers::CurrentLedger, Ledger, RecordsFilter};
use console::{
    account::{Address, ViewKey},
    network::{prelude::*, Testnet3},
    program::{Entry, Identifier, Literal, Plaintext, Value},
};
use synthesizer::{
    block::Block,
    store::{helpers::memory::ConsensusMemory, ConsensusStore},
    vm::VM,
    Program,
};

type CurrentNetwork = Testnet3;

#[cfg(test)]
pub(crate) mod test_helpers {
    use super::*;
    use console::{account::PrivateKey, network::Testnet3, prelude::TestRng};

    use once_cell::sync::OnceCell;

    type CurrentNetwork = Testnet3;
    pub(crate) type CurrentLedger = Ledger<CurrentNetwork, ConsensusMemory<CurrentNetwork>>;

    pub(crate) fn sample_genesis_private_key(rng: &mut TestRng) -> PrivateKey<CurrentNetwork> {
        static INSTANCE: OnceCell<PrivateKey<CurrentNetwork>> = OnceCell::new();
        *INSTANCE.get_or_init(|| {
            // Initialize a new caller.
            PrivateKey::<CurrentNetwork>::new(rng).unwrap()
        })
    }
}

fn sample_genesis_block() -> Block<CurrentNetwork> {
    Block::<CurrentNetwork>::from_bytes_le(CurrentNetwork::genesis_bytes()).unwrap()
}

#[test]
fn test_load() {
    let rng = &mut TestRng::default();

    // Sample the genesis private key.
    let private_key = crate::tests::test_helpers::sample_genesis_private_key(rng);
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
    let genesis = sample_genesis_block();

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
    // Load the genesis block.
    let genesis = sample_genesis_block();
    // Initialize the ledger with the genesis block.
    let ledger = CurrentLedger::load(genesis.clone(), None).unwrap();
    // Retrieve the genesis block.
    let block = ledger.get_block(0).unwrap();
    assert_eq!(genesis, block);

    // Construct the state path.
    let commitments = block.transactions().commitments().collect::<Vec<_>>();
    let commitment = commitments[0];

    let _state_path = ledger.get_state_path_for_commitment(commitment).unwrap();
}

#[test]
fn test_insufficient_finalize_fees() {
    let rng = &mut TestRng::default();

    // Sample the genesis private key.
    let private_key = test_helpers::sample_genesis_private_key(rng);
    let view_key = ViewKey::try_from(&private_key).unwrap();
    let address = Address::try_from(&private_key).unwrap();
    // Initialize the store.
    let store = ConsensusStore::<_, ConsensusMemory<_>>::open(None).unwrap();
    // Create a genesis block.
    let genesis = VM::from(store).unwrap().genesis(&private_key, rng).unwrap();
    // Initialize the ledger with the genesis block.
    let ledger = CurrentLedger::load(genesis, None).unwrap();

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
    let additional_fee = (credits, 0);

    // Deploy.
    let transaction = ledger.vm().deploy(&private_key, &program, additional_fee, None, rng).unwrap();
    // Verify.
    assert!(ledger.vm().verify_transaction(&transaction, None));

    // Construct the next block.
    let block = ledger.prepare_advance_to_next_block(&private_key, vec![transaction], None, rng).unwrap();
    // Advance to the next block.
    ledger.advance_to_next_block(&block).unwrap();
    assert_eq!(ledger.latest_height(), 1);
    assert_eq!(ledger.latest_hash(), block.hash());

    // Create a transfer transaction to produce a record with insufficient balance to pay for fees.
    let transfer_transaction = ledger.create_transfer(&private_key, address, 100, 0, None).unwrap();

    // Construct the next block.
    let block =
        ledger.prepare_advance_to_next_block(&private_key, vec![transfer_transaction.clone()], None, rng).unwrap();
    // Advance to the next block.
    ledger.advance_to_next_block(&block).unwrap();
    assert_eq!(ledger.latest_height(), 2);
    assert_eq!(ledger.latest_hash(), block.hash());

    // Execute the test program, without providing enough fees for finalize, and ensure that the ledger deems the transaction invalid.

    // Find records from the transfer transaction.
    let records = transfer_transaction
        .records()
        .map(|(_, record)| record.decrypt(&view_key))
        .collect::<Result<Vec<_>, _>>()
        .unwrap();

    // Retrieve the VM.
    let vm = ledger.vm();

    // Prepare the inputs.
    let inputs = [Value::<CurrentNetwork>::from_str("1u8").unwrap()].into_iter();

    // Check that the record has the correct balance.
    let insufficient_record = records[0].clone();
    if let Some(Entry::Private(Plaintext::Literal(Literal::U64(amount), _))) =
        &insufficient_record.data().get(&Identifier::from_str("microcredits").unwrap())
    {
        assert_eq!(**amount, 100)
    }
    // Ensure that we can't produce a transaction with a record that has insufficient balance to pay for fees.
    assert!(
        vm.execute(&private_key, ("dummy.aleo", "foo"), inputs.clone(), Some((insufficient_record, 0)), None, rng)
            .is_err()
    );

    let sufficient_record = records[1].clone();
    // Execute with enough fees.
    let transaction =
        vm.execute(&private_key, ("dummy.aleo", "foo"), inputs, Some((sufficient_record, 0)), None, rng).unwrap();
    // Verify.
    assert!(vm.verify_transaction(&transaction, None));

    // Ensure that the ledger deems the transaction valid.
    assert!(ledger.check_transaction_basic(&transaction, None).is_ok());
}
