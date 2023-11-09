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

use std::sync::Arc;
use std::thread;
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
use std::time::Instant;
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
fn test_insufficient_private_fees() {
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
fn test_insufficient_public_fees() {
    let rng = &mut TestRng::default();

    // Initialize the test environment.
    let crate::test_helpers::TestEnv { ledger, private_key, .. } = crate::test_helpers::sample_test_env(rng);

    // Sample recipient.
    let recipient_private_key = PrivateKey::new(rng).unwrap();
    let recipient_address = Address::try_from(&recipient_private_key).unwrap();

    // Fund the recipient with 1 million credits.
    {
        let inputs =
            [Value::from_str(&format!("{recipient_address}")).unwrap(), Value::from_str("1000000000000u64").unwrap()];
        let transaction = ledger
            .vm
            .execute(&private_key, ("credits.aleo", "transfer_public"), inputs.into_iter(), None, 0, None, rng)
            .unwrap();

        let block =
            ledger.prepare_advance_to_next_beacon_block(&private_key, vec![], vec![], vec![transaction], rng).unwrap();

        // Check that the next block is valid.
        ledger.check_next_block(&block).unwrap();
        // Add the deployment block to the ledger.
        ledger.advance_to_next_block(&block).unwrap();
    }

    println!("-----------");

    // Attempt to bond the node with insufficient public fees.
    {
        let inputs =
            [Value::from_str(&format!("{recipient_address}")).unwrap(), Value::from_str("1000000000000u64").unwrap()];
        let transaction = ledger
            .vm
            .execute(&recipient_private_key, ("credits.aleo", "bond_public"), inputs.into_iter(), None, 0, None, rng)
            .unwrap();

        let block =
            ledger.prepare_advance_to_next_beacon_block(&private_key, vec![], vec![], vec![transaction], rng).unwrap();

        // Check that the next block is valid.
        ledger.check_next_block(&block).unwrap();
        // Add the deployment block to the ledger.
        ledger.advance_to_next_block(&block).unwrap();
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
    ledger.vm().check_transaction(&transaction, None).unwrap();

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
    ledger.vm.check_transaction(&transaction, None).unwrap();
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
    ledger.vm().check_transaction(&transaction, None).unwrap();

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

#[test]
fn test_finalize_operation_spam() {
    const NUM_TRANSACTIONS: usize = 1;

    let rng = &mut TestRng::default();

    // Initialize the test environment.
    let crate::test_helpers::TestEnv { ledger, private_key, view_key, .. } = crate::test_helpers::sample_test_env(rng);

    // `child_spammer.aleo` source code
    let child_program = Program::<CurrentNetwork>::from_str(
        r"
program child_spammer.aleo;

mapping map:
	key as u8.public;
	value as u8.public;

function spam:
    async spam into r0;
    output r0 as child_spammer.aleo/spam.future;

finalize spam:
    set 0u8 into map[0u8];
    set 1u8 into map[1u8];
    set 2u8 into map[2u8];
    set 3u8 into map[3u8];
    set 4u8 into map[4u8];
    set 5u8 into map[5u8];
    set 6u8 into map[6u8];
    set 7u8 into map[7u8];
    set 8u8 into map[8u8];
    set 9u8 into map[9u8];
    set 10u8 into map[10u8];
    set 11u8 into map[11u8];
    set 12u8 into map[12u8];
    set 13u8 into map[13u8];
    set 14u8 into map[14u8];
    set 15u8 into map[15u8];",
    )
    .unwrap();

    // Create transaction deploying `child_spammer.aleo`
    let child_deploy_transaction = ledger.vm.deploy(&private_key, &child_program, None, 0, None, rng).unwrap();

    // Construct the next block.
    let child_deploy_transfer_block = ledger
        .prepare_advance_to_next_beacon_block(&private_key, vec![], vec![], vec![child_deploy_transaction], rng)
        .unwrap();

    // Check that the next block is valid.
    ledger.check_next_block(&child_deploy_transfer_block).unwrap();

    // Add the deployment block to the ledger.
    ledger.advance_to_next_block(&child_deploy_transfer_block).unwrap();

    // `parent_spammer.aleo` source code
    let parent_program = Program::<CurrentNetwork>::from_str(
        r"
import child_spammer.aleo;
program parent_spammer.aleo;

function main:
    call child_spammer.aleo/spam into r0;
    call child_spammer.aleo/spam into r1;
    call child_spammer.aleo/spam into r2;
    call child_spammer.aleo/spam into r3;
    call child_spammer.aleo/spam into r4;
    call child_spammer.aleo/spam into r5;
    call child_spammer.aleo/spam into r6;
    call child_spammer.aleo/spam into r7;
    call child_spammer.aleo/spam into r8;
    call child_spammer.aleo/spam into r9;
    call child_spammer.aleo/spam into r10;
    call child_spammer.aleo/spam into r11;
    call child_spammer.aleo/spam into r12;
    call child_spammer.aleo/spam into r13;
    async main r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 into r14;
    output r14 as parent_spammer.aleo/main.future;

finalize main:
    input r0 as child_spammer.aleo/spam.future;
    input r1 as child_spammer.aleo/spam.future;
    input r2 as child_spammer.aleo/spam.future;
    input r3 as child_spammer.aleo/spam.future;
    input r4 as child_spammer.aleo/spam.future;
    input r5 as child_spammer.aleo/spam.future;
    input r6 as child_spammer.aleo/spam.future;
    input r7 as child_spammer.aleo/spam.future;
    input r8 as child_spammer.aleo/spam.future;
    input r9 as child_spammer.aleo/spam.future;
    input r10 as child_spammer.aleo/spam.future;
    input r11 as child_spammer.aleo/spam.future;
    input r12 as child_spammer.aleo/spam.future;
    input r13 as child_spammer.aleo/spam.future;
    await r0;
    await r1;
    await r2;
    await r3;
    await r4;
    await r5;
    await r6;
    await r7;
    await r8;
    await r9;
    await r10;
    await r11;
    await r12;
    await r13;
",
    )
    .unwrap();

    // Create transaction deploying `parent_spammer.aleo`
    let parent_deploy_transaction = ledger.vm.deploy(&private_key, &parent_program, None, 0, None, rng).unwrap();

    // Construct the next block.
    let parent_deploy_transfer_block = ledger
        .prepare_advance_to_next_beacon_block(&private_key, vec![], vec![], vec![parent_deploy_transaction], rng)
        .unwrap();

    // Check that the next block is valid.
    ledger.check_next_block(&parent_deploy_transfer_block).unwrap();

    // Add the deployment block to the ledger.
    ledger.advance_to_next_block(&parent_deploy_transfer_block).unwrap();
    // `grandfather_spammer.aleo` source code
    let grandfather_program = Program::<CurrentNetwork>::from_str(
        r"
import child_spammer.aleo;
import parent_spammer.aleo;
program grandfather_spammer.aleo;



function outer_most_call:
    call parent_spammer.aleo/main into r0;
    call parent_spammer.aleo/main into r1;
    async outer_most_call r0 r1 into r2;
    output r2 as grandfather_spammer.aleo/outer_most_call.future;

finalize outer_most_call:
    input r0 as parent_spammer.aleo/main.future;
    input r1 as parent_spammer.aleo/main.future;
    await r0;
    await r1;
",
    )
    .unwrap();

    // Create transaction deploying `grandfather_spammer.aleo`
    let grandfather_deploy_transaction =
        ledger.vm.deploy(&private_key, &grandfather_program, None, 0, None, rng).unwrap();

    // Construct the next block.
    let grandfather_deploy_transfer_block = ledger
        .prepare_advance_to_next_beacon_block(&private_key, vec![], vec![], vec![grandfather_deploy_transaction], rng)
        .unwrap();

    // Check that the next block is valid.
    ledger.check_next_block(&grandfather_deploy_transfer_block).unwrap();

    // Add the deployment block to the ledger.
    ledger.advance_to_next_block(&grandfather_deploy_transfer_block).unwrap();

    // Helper function to assemble grandfather execute transaction
    fn create_transaction(l: &CurrentLedger, pk: &PrivateKey<CurrentNetwork>) -> Transaction<CurrentNetwork> {
        let r = &mut TestRng::default();
        // Append an `grandfather_spam.aleo/outer_most_call` execute transaction to the list of transactions.
        let execute_inputs: Vec<Value<CurrentNetwork>> = Vec::new();
        l.vm.execute(pk, ("grandfather_spammer.aleo", "outer_most_call"), execute_inputs.into_iter(), None, 0, None, r)
            .unwrap()
    }

    let start = Instant::now();

    // Spawn threads to split workload
    let mut grandfather_execute_transactions = Vec::new();
    for i in 0..NUM_TRANSACTIONS {
        grandfather_execute_transactions.push(create_transaction(&ledger, &private_key));

        // Print out progress
        println!("------------------------------------------------------------------");
        println!("------------------------------------------------------------------");
        println!("------------------------------------------------------------------");
        println!("------------------------------------------------------------------");
        println!("{}/{} completed!", i, NUM_TRANSACTIONS);
        println!("------------------------------------------------------------------");
        println!("------------------------------------------------------------------");
        println!("------------------------------------------------------------------");
        println!("------------------------------------------------------------------");
    }

    // Construct the next block.
    let grandfather_execute_transfer_block = ledger
        .prepare_advance_to_next_beacon_block(&private_key, vec![], vec![], grandfather_execute_transactions, rng)
        .unwrap();

    // Check that the next block is valid.
    ledger.check_next_block(&grandfather_execute_transfer_block).unwrap();

    // Add the deployment block to the ledger.
    ledger.advance_to_next_block(&grandfather_execute_transfer_block).unwrap();

    // Stop the timer
    let duration = start.elapsed();

    // Print the duration
    println!("Time elapsed is: {:?}", duration);
    println!("Time elapsed per transactions is {:?}", duration / NUM_TRANSACTIONS as u32);
}

#[test]
fn test_parallel_finalize_operation_spam() {
    const NUM_TRANSACTIONS: usize = 20;

    let rng = &mut TestRng::default();

    // Initialize the test environment.
    let crate::test_helpers::TestEnv { ledger, private_key, view_key, .. } = crate::test_helpers::sample_test_env(rng);

    // `child_spammer.aleo` source code
    let child_program = Program::<CurrentNetwork>::from_str(
        r"
program child_spammer.aleo;

mapping map:
	key as u8.public;
	value as u8.public;

function spam:
    async spam into r0;
    output r0 as child_spammer.aleo/spam.future;

finalize spam:
    set 0u8 into map[0u8];
    set 1u8 into map[1u8];
    set 2u8 into map[2u8];
    set 3u8 into map[3u8];
    set 4u8 into map[4u8];
    set 5u8 into map[5u8];
    set 6u8 into map[6u8];
    set 7u8 into map[7u8];
    set 8u8 into map[8u8];
    set 9u8 into map[9u8];
    set 10u8 into map[10u8];
    set 11u8 into map[11u8];
    set 12u8 into map[12u8];
    set 13u8 into map[13u8];
    set 14u8 into map[14u8];
    set 15u8 into map[15u8];",
    )
        .unwrap();

    // Create transaction deploying `child_spammer.aleo`
    let child_deploy_transaction = ledger.vm.deploy(&private_key, &child_program, None, 0, None, rng).unwrap();

    // Construct the next block.
    let child_deploy_transfer_block = ledger
        .prepare_advance_to_next_beacon_block(&private_key, vec![], vec![], vec![child_deploy_transaction], rng)
        .unwrap();

    // Check that the next block is valid.
    ledger.check_next_block(&child_deploy_transfer_block).unwrap();

    // Add the deployment block to the ledger.
    ledger.advance_to_next_block(&child_deploy_transfer_block).unwrap();

    // `parent_spammer.aleo` source code
    let parent_program = Program::<CurrentNetwork>::from_str(
        r"
import child_spammer.aleo;
program parent_spammer.aleo;

function main:
    call child_spammer.aleo/spam into r0;
    call child_spammer.aleo/spam into r1;
    call child_spammer.aleo/spam into r2;
    call child_spammer.aleo/spam into r3;
    call child_spammer.aleo/spam into r4;
    call child_spammer.aleo/spam into r5;
    call child_spammer.aleo/spam into r6;
    call child_spammer.aleo/spam into r7;
    call child_spammer.aleo/spam into r8;
    call child_spammer.aleo/spam into r9;
    call child_spammer.aleo/spam into r10;
    call child_spammer.aleo/spam into r11;
    call child_spammer.aleo/spam into r12;
    call child_spammer.aleo/spam into r13;
    async main r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 into r14;
    output r14 as parent_spammer.aleo/main.future;

finalize main:
    input r0 as child_spammer.aleo/spam.future;
    input r1 as child_spammer.aleo/spam.future;
    input r2 as child_spammer.aleo/spam.future;
    input r3 as child_spammer.aleo/spam.future;
    input r4 as child_spammer.aleo/spam.future;
    input r5 as child_spammer.aleo/spam.future;
    input r6 as child_spammer.aleo/spam.future;
    input r7 as child_spammer.aleo/spam.future;
    input r8 as child_spammer.aleo/spam.future;
    input r9 as child_spammer.aleo/spam.future;
    input r10 as child_spammer.aleo/spam.future;
    input r11 as child_spammer.aleo/spam.future;
    input r12 as child_spammer.aleo/spam.future;
    input r13 as child_spammer.aleo/spam.future;
    await r0;
    await r1;
    await r2;
    await r3;
    await r4;
    await r5;
    await r6;
    await r7;
    await r8;
    await r9;
    await r10;
    await r11;
    await r12;
    await r13;
",
    )
        .unwrap();

    // Create transaction deploying `parent_spammer.aleo`
    let parent_deploy_transaction = ledger.vm.deploy(&private_key, &parent_program, None, 0, None, rng).unwrap();

    // Construct the next block.
    let parent_deploy_transfer_block = ledger
        .prepare_advance_to_next_beacon_block(&private_key, vec![], vec![], vec![parent_deploy_transaction], rng)
        .unwrap();

    // Check that the next block is valid.
    ledger.check_next_block(&parent_deploy_transfer_block).unwrap();

    // Add the deployment block to the ledger.
    ledger.advance_to_next_block(&parent_deploy_transfer_block).unwrap();
    // `grandfather_spammer.aleo` source code
    let grandfather_program = Program::<CurrentNetwork>::from_str(
        r"
import child_spammer.aleo;
import parent_spammer.aleo;
program grandfather_spammer.aleo;



function outer_most_call:
    call parent_spammer.aleo/main into r0;
    call parent_spammer.aleo/main into r1;
    async outer_most_call r0 r1 into r2;
    output r2 as grandfather_spammer.aleo/outer_most_call.future;

finalize outer_most_call:
    input r0 as parent_spammer.aleo/main.future;
    input r1 as parent_spammer.aleo/main.future;
    await r0;
    await r1;
",
    )
        .unwrap();

    // Create transaction deploying `grandfather_spammer.aleo`
    let grandfather_deploy_transaction =
        ledger.vm.deploy(&private_key, &grandfather_program, None, 0, None, rng).unwrap();

    // Construct the next block.
    let grandfather_deploy_transfer_block = ledger
        .prepare_advance_to_next_beacon_block(&private_key, vec![], vec![], vec![grandfather_deploy_transaction], rng)
        .unwrap();

    // Check that the next block is valid.
    ledger.check_next_block(&grandfather_deploy_transfer_block).unwrap();

    // Add the deployment block to the ledger.
    ledger.advance_to_next_block(&grandfather_deploy_transfer_block).unwrap();

    // Helper function to assemble grandfather execute transaction
    fn create_transaction(l:&CurrentLedger, pk:&PrivateKey<CurrentNetwork>, r: &mut TestRng) -> Transaction<CurrentNetwork> {
        // Append an `grandfather_spam.aleo/outer_most_call` execute transaction to the list of transactions.
        let execute_inputs: Vec<Value<CurrentNetwork>> = Vec::new();
        l
            .vm
            .execute(pk, ("grandfather_spammer.aleo", "outer_most_call"), execute_inputs.into_iter(), None, 0, None, r)
            .unwrap()
    }

    // Helper function to complete threads portion of workload
    fn complete_threads_portion_of_workload(l: &CurrentLedger, pk:&PrivateKey<CurrentNetwork>, num_jobs: usize, thread_id: usize) ->Vec<Transaction<CurrentNetwork>> {
        let r = &mut TestRng::default();
        let mut grandfather_execute_transactions: Vec<Transaction<CurrentNetwork>> = Vec::new();
        for i in 0..num_jobs {
            grandfather_execute_transactions.push(create_transaction(l, pk, r));

            // Print out progress
            println!("------------------------------------------------------------------");
            println!("Thread: {} has completed {}/{} tasks!", thread_id, i, num_jobs);
            println!("------------------------------------------------------------------");
        }
        grandfather_execute_transactions
    }

    // Compute parallelization logic
    let mut handles = Vec::new();
    let num_cpus = num_cpus::get();
    let work_per_thread = (NUM_TRANSACTIONS + num_cpus - 1) / num_cpus; // Round up

    // Start the timer
    let start = Instant::now();


    let ledger_clone = ledger.clone();

    // Spawn threads to split workload
    for i in 0..num_cpus {
        let ledger_ref = ledger_clone.clone();
        let handle = thread::spawn(move || {
            complete_threads_portion_of_workload(&ledger_ref, &private_key, work_per_thread, i)
        });
        handles.push(handle);
    }

    let mut results = Vec::new();

    // Collect the results from each thread
    for handle in handles {
        let result = handle.join().unwrap();
        results.push(result);
    }

    let assembled_transaction_list = results.concat();

    // Construct the next block.
    let grandfather_execute_transfer_block = ledger
        .prepare_advance_to_next_beacon_block(&private_key, vec![], vec![], assembled_transaction_list, rng)
        .unwrap();

    // Check that the next block is valid.
    ledger.check_next_block(&grandfather_execute_transfer_block).unwrap();

    // Add the deployment block to the ledger.
    ledger.advance_to_next_block(&grandfather_execute_transfer_block).unwrap();

    // Stop the timer
    let duration = start.elapsed();

    // Print the duration
    println!("Time elapsed is: {:?}", duration);
    println!("Time elapsed per transactions is {:?}", duration / (num_cpus * work_per_thread) as u32);
    println!("Num cpus: {}",num_cpus);
    println!("Work per thread: {}", work_per_thread);;
}
