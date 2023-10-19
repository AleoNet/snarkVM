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
    account::{Address, PrivateKey},
    network::prelude::*,
    program::{Entry, Identifier, Literal, Plaintext, ProgramID, Value},
};
use ledger_block::{ConfirmedTransaction, Rejected, Transaction};
use ledger_store::{helpers::memory::ConsensusMemory, ConsensusStore};
use synthesizer::{program::Program, vm::VM};

#[test]
fn test_load() {
    let rng = &mut TestRng::default();

    // Sample the genesis private key.
    let private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
    // Initialize the store.
    let store = ConsensusStore::<_, ConsensusMemory<_>>::open(None).unwrap();
    // Create a genesis block.
    let genesis = VM::from(store).unwrap().genesis_beacon(&private_key, rng).unwrap();

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
fn test_insufficient_fees() {
    let rng = &mut TestRng::default();

    // Initialize the test environment.
    let crate::test_helpers::TestEnv { ledger, private_key, view_key, address, .. } =
        crate::test_helpers::sample_test_env(rng);

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
    let record_1 = records[0].clone();
    let record_2 = records[1].clone();

    // Check fee amount requirements for `split` calls.
    {
        // Prepare a `split` execution without a fee.
        let inputs = [Value::Record(record_1.clone()), Value::from_str("100u64").unwrap()];
        let authorization =
            ledger.vm.authorize(&private_key, "credits.aleo", "split", inputs.into_iter(), rng).unwrap();
        let split_transaction_without_fee = ledger.vm.execute_authorization(authorization, None, None, rng).unwrap();
        assert!(ledger.check_transaction_basic(&split_transaction_without_fee, None).is_ok());
    }

    // Check fee amount requirements for executions.
    {
        // Prepare an execution without a fee.
        let inputs = [
            Value::Record(record_1),
            Value::from_str(&format!("{address}")).unwrap(),
            Value::from_str("100u64").unwrap(),
        ];
        let authorization =
            ledger.vm.authorize(&private_key, "credits.aleo", "transfer_private", inputs.into_iter(), rng).unwrap();
        let transaction_without_fee = ledger.vm.execute_authorization(authorization, None, None, rng).unwrap();
        let execution = transaction_without_fee.execution().unwrap();

        // Check that a transaction with sufficient fee will succeed.
        let fee_authorization = ledger
            .vm
            .authorize_fee_private(
                &private_key,
                record_2.clone(),
                10_000_000,
                1_000,
                execution.to_execution_id().unwrap(),
                rng,
            )
            .unwrap();
        let fee = ledger.vm.execute_fee_authorization(fee_authorization, None, rng).unwrap();
        let sufficient_fee_transaction = Transaction::from_execution(execution.clone(), Some(fee)).unwrap();
        assert!(ledger.check_transaction_basic(&sufficient_fee_transaction, None).is_ok());

        // Check that a transaction with insufficient fee will fail.
        let insufficient_fee_authorization = ledger
            .vm
            .authorize_fee_private(&private_key, record_2.clone(), 1, 0, execution.to_execution_id().unwrap(), rng)
            .unwrap();
        let insufficient_fee = ledger.vm.execute_fee_authorization(insufficient_fee_authorization, None, rng).unwrap();
        let insufficient_fee_transaction =
            Transaction::from_execution(execution.clone(), Some(insufficient_fee)).unwrap();
        assert!(ledger.check_transaction_basic(&insufficient_fee_transaction, None).is_err());
    }

    // Check fee amount requirements for deployment.

    {
        // Deploy a test program to the ledger.
        let program = Program::<CurrentNetwork>::from_str(
            r"
program dummy.aleo;
function foo:
    input r0 as u8.private;
    async foo r0 into r1;
    output r1 as dummy.aleo/foo.future;
finalize foo:
    input r0 as u8.public;
    add r0 r0 into r1;",
        )
        .unwrap();

        // Check that a deployment transaction with sufficient fee will succeed.
        let transaction = ledger.vm.deploy(&private_key, &program, Some(record_2.clone()), 0, None, rng).unwrap();
        assert!(ledger.check_transaction_basic(&transaction, None).is_ok());

        // Check that a deployment transaction with insufficient fee will fail.
        let deployment = transaction.deployment().unwrap();
        let insufficient_fee_authorization = ledger
            .vm
            .authorize_fee_private(&private_key, record_2, 1, 0, deployment.to_deployment_id().unwrap(), rng)
            .unwrap();
        let insufficient_fee = ledger.vm.execute_fee_authorization(insufficient_fee_authorization, None, rng).unwrap();
        let insufficient_fee_transaction =
            Transaction::from_deployment(*transaction.owner().unwrap(), deployment.clone(), insufficient_fee).unwrap();
        assert!(ledger.check_transaction_basic(&insufficient_fee_transaction, None).is_err());
    }
}

#[test]
fn test_insufficient_finalize_fees() {
    let rng = &mut TestRng::default();

    // Initialize the test environment.
    let crate::test_helpers::TestEnv { ledger, private_key, view_key, address, .. } =
        crate::test_helpers::sample_test_env(rng);

    // Deploy a test program to the ledger.
    let program = Program::<CurrentNetwork>::from_str(
        r"
program dummy.aleo;
function foo:
    input r0 as u8.private;
    async foo r0 into r1;
    output r1 as dummy.aleo/foo.future;
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
    let credits = Some(records.values().next().unwrap().clone());

    // Deploy.
    let transaction = ledger.vm.deploy(&private_key, &program, credits, 0, None, rng).unwrap();
    // Verify.
    assert!(ledger.vm().verify_transaction(&transaction, None));

    // Construct the next block.
    let block =
        ledger.prepare_advance_to_next_beacon_block(&private_key, vec![], vec![], vec![transaction], rng).unwrap();
    // Advance to the next block.
    ledger.advance_to_next_block(&block).unwrap();
    assert_eq!(ledger.latest_height(), 1);
    assert_eq!(ledger.latest_hash(), block.hash());

    // Create a transfer transaction to produce a record with insufficient balance to pay for fees.
    let transfer_transaction = ledger.create_transfer(&private_key, address, 100, 0, None).unwrap();

    // Construct the next block.
    let block = ledger
        .prepare_advance_to_next_beacon_block(&private_key, vec![], vec![], vec![transfer_transaction.clone()], rng)
        .unwrap();
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
        ledger
            .vm
            .execute(&private_key, ("dummy.aleo", "foo"), inputs.clone(), Some(insufficient_record), 0, None, rng)
            .is_err()
    );

    let sufficient_record = records[1].clone();
    // Execute with enough fees.
    let transaction =
        ledger.vm.execute(&private_key, ("dummy.aleo", "foo"), inputs, Some(sufficient_record), 0, None, rng).unwrap();
    // Verify.
    assert!(ledger.vm.verify_transaction(&transaction, None));
    // Ensure that the ledger deems the transaction valid.
    assert!(ledger.check_transaction_basic(&transaction, None).is_ok());
}

#[test]
fn test_rejected_execution() {
    let rng = &mut TestRng::default();

    // Initialize the test environment.
    let crate::test_helpers::TestEnv { ledger, private_key, view_key, .. } = crate::test_helpers::sample_test_env(rng);

    // Deploy a test program to the ledger.
    let program_id = "test_rejected_execute.aleo";
    let program = Program::<CurrentNetwork>::from_str(&format!(
        "
program {program_id};

function failed_assert:
    async failed_assert into r0;
    output r0 as {program_id}/failed_assert.future;

finalize failed_assert:
    assert.eq false true;"
    ))
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
    let record_1 = records[0].clone();
    let record_2 = records[1].clone();

    // Deploy the program.
    let deployment_transaction = ledger.vm().deploy(&private_key, &program, Some(record_1), 0, None, rng).unwrap();

    // Construct the deployment block.
    let deployment_block = ledger
        .prepare_advance_to_next_beacon_block(&private_key, vec![], vec![], vec![deployment_transaction], rng)
        .unwrap();

    // Check that the next block is valid.
    ledger.check_next_block(&deployment_block).unwrap();

    // Add the deployment block to the ledger.
    ledger.advance_to_next_block(&deployment_block).unwrap();

    // Construct a transaction that will cause error from an assert call in `finalize`.
    let failed_assert_transaction = ledger
        .vm()
        .execute(
            &private_key,
            (program_id, "failed_assert"),
            Vec::<Value<_>>::new().into_iter(),
            Some(record_2),
            0,
            None,
            rng,
        )
        .unwrap();
    let failed_assert_transaction_id = failed_assert_transaction.id();

    // Construct the next block containing the new transaction.
    let next_block = ledger
        .prepare_advance_to_next_beacon_block(
            &private_key,
            vec![],
            vec![],
            vec![failed_assert_transaction.clone()],
            rng,
        )
        .unwrap();

    // Check that the block contains 1 rejected execution.
    assert_eq!(next_block.transactions().len(), 1);
    let confirmed_transaction = next_block.transactions().iter().next().unwrap();
    assert!(confirmed_transaction.is_rejected());
    if let Transaction::Execute(_, execution, fee) = failed_assert_transaction {
        let fee_transaction = Transaction::from_fee(fee.unwrap()).unwrap();
        let expected_confirmed_transaction =
            ConfirmedTransaction::RejectedExecute(0, fee_transaction, Rejected::new_execution(execution), vec![]);

        assert_eq!(confirmed_transaction, &expected_confirmed_transaction);
    }

    // Check that the unconfirmed transaction ID of the rejected execution is correct.
    assert_eq!(confirmed_transaction.to_unconfirmed_transaction_id().unwrap(), failed_assert_transaction_id);

    // Check that the next block is valid.
    ledger.check_next_block(&next_block).unwrap();

    // Add the block with the rejected transaction to the ledger.
    ledger.advance_to_next_block(&next_block).unwrap();
}

#[test]
fn test_deploy_with_public_fees() {
    let rng = &mut TestRng::default();

    // Initialize the test environment.
    let crate::test_helpers::TestEnv { ledger, private_key, .. } = crate::test_helpers::sample_test_env(rng);

    // Deploy a test program to the ledger.
    let program_id = ProgramID::<CurrentNetwork>::from_str("dummy_program.aleo").unwrap();
    let program = Program::<CurrentNetwork>::from_str(&format!(
        "
program {program_id};
function foo:
    input r0 as u8.private;
    async foo r0 into r1;
    output r1 as {program_id}/foo.future;
finalize foo:
    input r0 as u8.public;
    add r0 r0 into r1;",
    ))
    .unwrap();

    // Deploy.
    let transaction = ledger.vm.deploy(&private_key, &program, None, 0, None, rng).unwrap();
    // Verify.
    assert!(ledger.vm().verify_transaction(&transaction, None));

    // Construct the next block.
    let block =
        ledger.prepare_advance_to_next_beacon_block(&private_key, vec![], vec![], vec![transaction], rng).unwrap();
    // Advance to the next block.
    ledger.advance_to_next_block(&block).unwrap();
    assert_eq!(ledger.latest_height(), 1);
    assert_eq!(ledger.latest_hash(), block.hash());

    assert_eq!(program, ledger.get_program(program_id).unwrap())
}

#[test]
fn test_bond_and_unbond_validator() {
    let rng = &mut TestRng::default();

    // Initialize the test environment.
    let crate::test_helpers::TestEnv { ledger, private_key, .. } = crate::test_helpers::sample_test_env(rng);

    // Sample new account for the new committee member.
    let new_member_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
    let new_member_address = Address::try_from(&new_member_private_key).unwrap();

    // Fund the new committee member.
    let inputs = [
        Value::from_str(&format!("{new_member_address}")).unwrap(),
        Value::from_str("10000000000000u64").unwrap(), // 10 million credits.
    ];
    let transfer_transaction = ledger
        .vm
        .execute(&private_key, ("credits.aleo", "transfer_public"), inputs.iter(), None, 0, None, rng)
        .unwrap();

    // Construct the next block.
    let transfer_block = ledger
        .prepare_advance_to_next_beacon_block(&private_key, vec![], vec![], vec![transfer_transaction], rng)
        .unwrap();

    // Check that the next block is valid.
    ledger.check_next_block(&transfer_block).unwrap();

    // Add the deployment block to the ledger.
    ledger.advance_to_next_block(&transfer_block).unwrap();

    // Construct the bond public
    let bond_amount = 1000000000000u64; // 1 million credits.
    let inputs = [
        Value::from_str(&format!("{new_member_address}")).unwrap(),
        Value::from_str(&format!("{bond_amount}u64")).unwrap(),
    ];
    let bond_public_transaction = ledger
        .vm
        .execute(&new_member_private_key, ("credits.aleo", "bond_public"), inputs.iter(), None, 0, None, rng)
        .unwrap();

    // Construct the next block.
    let bond_public_block = ledger
        .prepare_advance_to_next_beacon_block(&private_key, vec![], vec![], vec![bond_public_transaction], rng)
        .unwrap();

    // Check that the committee does not include the new member.
    let committee = ledger.latest_committee().unwrap();
    assert!(!committee.is_committee_member(new_member_address));

    // Check that the next block is valid.
    ledger.check_next_block(&bond_public_block).unwrap();

    // Add the bond public block to the ledger.
    ledger.advance_to_next_block(&bond_public_block).unwrap();

    // Check that the committee is updated with the new member.
    let committee = ledger.latest_committee().unwrap();
    assert!(committee.is_committee_member(new_member_address));

    // Construct the bond public
    let unbond_amount = committee.get_stake(new_member_address); // 1 million credits.
    let inputs = [Value::from_str(&format!("{unbond_amount}u64")).unwrap()];
    let unbond_public_transaction = ledger
        .vm
        .execute(&new_member_private_key, ("credits.aleo", "unbond_public"), inputs.iter(), None, 0, None, rng)
        .unwrap();

    // Construct the next block.
    let unbond_public_block = ledger
        .prepare_advance_to_next_beacon_block(&private_key, vec![], vec![], vec![unbond_public_transaction], rng)
        .unwrap();

    // Check that the next block is valid.
    ledger.check_next_block(&unbond_public_block).unwrap();

    // Add the bond public block to the ledger.
    ledger.advance_to_next_block(&unbond_public_block).unwrap();

    // Check that the committee does not include the new member.
    let committee = ledger.latest_committee().unwrap();
    assert!(!committee.is_committee_member(new_member_address));
}
