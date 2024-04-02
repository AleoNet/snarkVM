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
    advance::split_candidate_solutions,
    test_helpers::{CurrentLedger, CurrentNetwork},
    Ledger,
    RecordsFilter,
};
use aleo_std::StorageMode;
use console::{
    account::{Address, PrivateKey},
    network::prelude::*,
    program::{Entry, Identifier, Literal, Plaintext, ProgramID, Value},
};
use ledger_block::{ConfirmedTransaction, Rejected, Transaction};
use ledger_committee::{Committee, MIN_VALIDATOR_STAKE};
use ledger_store::{helpers::memory::ConsensusMemory, ConsensusStore};
use synthesizer::{program::Program, vm::VM, Stack};

use indexmap::IndexMap;

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
    let ledger = CurrentLedger::load(genesis.clone(), StorageMode::Production).unwrap();
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
    let ledger = CurrentLedger::load_unchecked(genesis.clone(), StorageMode::Production).unwrap();
    assert_eq!(ledger.latest_hash(), genesis.hash());
    assert_eq!(ledger.latest_height(), genesis.height());
    assert_eq!(ledger.latest_round(), genesis.round());
    assert_eq!(ledger.latest_block(), genesis);

    // Initialize the ledger with the genesis block.
    let ledger = CurrentLedger::load(genesis.clone(), StorageMode::Production).unwrap();
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
        let authorization = ledger.vm.authorize(&private_key, "credits.aleo", "split", inputs, rng).unwrap();
        let split_transaction_without_fee = ledger.vm.execute_authorization(authorization, None, None, rng).unwrap();
        assert!(ledger.check_transaction_basic(&split_transaction_without_fee, None, rng).is_ok());
    }

    // Check fee amount requirements for executions.
    {
        // Prepare an execution without a fee.
        let inputs = [
            Value::Record(record_1),
            Value::from_str(&format!("{address}")).unwrap(),
            Value::from_str("100u64").unwrap(),
        ];
        let authorization = ledger.vm.authorize(&private_key, "credits.aleo", "transfer_private", inputs, rng).unwrap();
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
        assert!(ledger.check_transaction_basic(&sufficient_fee_transaction, None, rng).is_ok());

        // Check that a transaction with insufficient fee will fail.
        let insufficient_fee_authorization = ledger
            .vm
            .authorize_fee_private(&private_key, record_2.clone(), 1, 0, execution.to_execution_id().unwrap(), rng)
            .unwrap();
        let insufficient_fee = ledger.vm.execute_fee_authorization(insufficient_fee_authorization, None, rng).unwrap();
        let insufficient_fee_transaction =
            Transaction::from_execution(execution.clone(), Some(insufficient_fee)).unwrap();
        assert!(ledger.check_transaction_basic(&insufficient_fee_transaction, None, rng).is_err());
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
        assert!(ledger.check_transaction_basic(&transaction, None, rng).is_ok());

        // Check that a deployment transaction with insufficient fee will fail.
        let deployment = transaction.deployment().unwrap();
        let insufficient_fee_authorization = ledger
            .vm
            .authorize_fee_private(&private_key, record_2, 1, 0, deployment.to_deployment_id().unwrap(), rng)
            .unwrap();
        let insufficient_fee = ledger.vm.execute_fee_authorization(insufficient_fee_authorization, None, rng).unwrap();
        let insufficient_fee_transaction =
            Transaction::from_deployment(*transaction.owner().unwrap(), deployment.clone(), insufficient_fee).unwrap();
        assert!(ledger.check_transaction_basic(&insufficient_fee_transaction, None, rng).is_err());
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
        ledger.check_next_block(&block, rng).unwrap();
        // Add the deployment block to the ledger.
        ledger.advance_to_next_block(&block).unwrap();
    }

    println!("-----------");

    // Attempt to bond the node with insufficient public fees.
    {
        let inputs = [
            Value::from_str(&format!("{recipient_address}")).unwrap(),
            Value::from_str(&format!("{recipient_address}")).unwrap(),
            Value::from_str("1000000000000u64").unwrap(),
        ];
        let transaction = ledger
            .vm
            .execute(&recipient_private_key, ("credits.aleo", "bond_public"), inputs.into_iter(), None, 0, None, rng)
            .unwrap();

        let block =
            ledger.prepare_advance_to_next_beacon_block(&private_key, vec![], vec![], vec![transaction], rng).unwrap();

        // Check that the next block is valid.
        ledger.check_next_block(&block, rng).unwrap();
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
    ledger.vm().check_transaction(&transaction, None, rng).unwrap();

    // Construct the next block.
    let block =
        ledger.prepare_advance_to_next_beacon_block(&private_key, vec![], vec![], vec![transaction], rng).unwrap();
    // Advance to the next block.
    ledger.advance_to_next_block(&block).unwrap();
    assert_eq!(ledger.latest_height(), 1);
    assert_eq!(ledger.latest_hash(), block.hash());

    // Create a transfer transaction to produce a record with insufficient balance to pay for fees.
    let transfer_transaction = ledger.create_transfer(&private_key, address, 100, 0, None, rng).unwrap();

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
    ledger.vm.check_transaction(&transaction, None, rng).unwrap();
    // Ensure that the ledger deems the transaction valid.
    assert!(ledger.check_transaction_basic(&transaction, None, rng).is_ok());
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
    ledger.check_next_block(&deployment_block, rng).unwrap();

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
    ledger.check_next_block(&next_block, rng).unwrap();

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
    ledger.vm().check_transaction(&transaction, None, rng).unwrap();

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
        Value::from_str("20000000000000u64").unwrap(), // 20 million credits.
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
    ledger.check_next_block(&transfer_block, rng).unwrap();

    // Add the deployment block to the ledger.
    ledger.advance_to_next_block(&transfer_block).unwrap();

    // Construct the bond public
    let bond_amount = MIN_VALIDATOR_STAKE;
    let inputs = [
        Value::from_str(&format!("{new_member_address}")).unwrap(),
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
    ledger.check_next_block(&bond_public_block, rng).unwrap();

    // Add the bond public block to the ledger.
    ledger.advance_to_next_block(&bond_public_block).unwrap();

    // Check that the committee is updated with the new member.
    let committee = ledger.latest_committee().unwrap();
    assert!(committee.is_committee_member(new_member_address));

    // Check that number of validators in the `metadata` mapping in `credtis.aleo` is updated.
    let program_id = ProgramID::<CurrentNetwork>::from_str("credits.aleo").unwrap();
    let metadata_mapping_name = Identifier::from_str("metadata").unwrap();
    let key = Plaintext::<CurrentNetwork>::from_str("aleo1qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq3ljyzc")
        .unwrap();
    let num_validators = match ledger
        .vm()
        .finalize_store()
        .get_value_confirmed(program_id, metadata_mapping_name, &key)
        .unwrap()
        .unwrap()
    {
        Value::Plaintext(Plaintext::Literal(Literal::U32(num_validators), _)) => *num_validators as usize,
        _ => panic!("Unexpected value type"),
    };
    assert_eq!(num_validators, committee.num_members());

    // Construct the bond public
    let unbond_amount = committee.get_stake(new_member_address);
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
    ledger.check_next_block(&unbond_public_block, rng).unwrap();

    // Add the bond public block to the ledger.
    ledger.advance_to_next_block(&unbond_public_block).unwrap();

    // Check that the committee does not include the new member.
    let committee = ledger.latest_committee().unwrap();
    assert!(!committee.is_committee_member(new_member_address));

    // Check that number of validators in the `metadata` mapping in `credtis.aleo` is updated.
    let program_id = ProgramID::<CurrentNetwork>::from_str("credits.aleo").unwrap();
    let metadata_mapping_name = Identifier::from_str("metadata").unwrap();
    let key = Plaintext::<CurrentNetwork>::from_str("aleo1qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq3ljyzc")
        .unwrap();
    let num_validators = match ledger
        .vm()
        .finalize_store()
        .get_value_confirmed(program_id, metadata_mapping_name, &key)
        .unwrap()
        .unwrap()
    {
        Value::Plaintext(Plaintext::Literal(Literal::U32(num_validators), _)) => *num_validators as usize,
        _ => panic!("Unexpected value type"),
    };
    assert_eq!(num_validators, committee.num_members());
}

#[test]
fn test_aborted_transaction_indexing() {
    let rng = &mut TestRng::default();

    // Initialize the test environment.
    let crate::test_helpers::TestEnv { ledger, private_key, .. } = crate::test_helpers::sample_test_env(rng);

    // Sample a recipient account.
    let recipient_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
    let recipient_address = Address::try_from(&recipient_private_key).unwrap();

    // Sample another recipient account.
    let recipient_private_key_2 = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
    let recipient_address_2 = Address::try_from(&recipient_private_key_2).unwrap();

    // Fund a new address.
    let inputs = [Value::from_str(&format!("{recipient_address}")).unwrap(), Value::from_str("185000u64").unwrap()];
    let transfer_transaction = ledger
        .vm
        .execute(&private_key, ("credits.aleo", "transfer_public"), inputs.iter(), None, 0, None, rng)
        .unwrap();

    // Construct the next block.
    let transfer_block = ledger
        .prepare_advance_to_next_beacon_block(&private_key, vec![], vec![], vec![transfer_transaction], rng)
        .unwrap();

    // Check that the next block is valid.
    ledger.check_next_block(&transfer_block, rng).unwrap();

    // Add the deployment block to the ledger.
    ledger.advance_to_next_block(&transfer_block).unwrap();

    // Send a transaction that will be aborted due to insufficient fee.
    let inputs = [Value::from_str(&format!("{recipient_address_2}")).unwrap(), Value::from_str("1u64").unwrap()];
    let transfer_transaction = ledger
        .vm
        .execute(&recipient_private_key_2, ("credits.aleo", "transfer_public"), inputs.iter(), None, 0, None, rng)
        .unwrap();
    let aborted_transaction_id = transfer_transaction.id();

    // Create another arbitrary transaction.
    let inputs = [Value::from_str(&format!("{recipient_address_2}")).unwrap(), Value::from_str("1u64").unwrap()];
    let transfer_transaction_2 = ledger
        .vm
        .execute(&private_key, ("credits.aleo", "transfer_public"), inputs.iter(), None, 0, None, rng)
        .unwrap();

    // Create a block.
    let block = ledger
        .prepare_advance_to_next_beacon_block(
            &private_key,
            vec![],
            vec![],
            vec![transfer_transaction, transfer_transaction_2],
            rng,
        )
        .unwrap();

    // Check that the block contains the aborted transaction.
    assert_eq!(block.aborted_transaction_ids(), &[aborted_transaction_id]);

    // Check that the next block is valid.
    ledger.check_next_block(&block, rng).unwrap();

    // Add the deployment block to the ledger.
    ledger.advance_to_next_block(&block).unwrap();
}

#[test]
fn test_aborted_solution_ids() {
    let rng = &mut TestRng::default();

    // Initialize the test environment.
    let crate::test_helpers::TestEnv { ledger, private_key, address, .. } = crate::test_helpers::sample_test_env(rng);

    // Retrieve the puzzle parameters.
    let puzzle = ledger.puzzle();
    let latest_epoch_hash = ledger.latest_epoch_hash().unwrap();
    let minimum_proof_target = ledger.latest_proof_target();

    // Create a solution that is less than the minimum proof target.
    let mut invalid_solution = puzzle.prove(latest_epoch_hash, address, rng.gen(), None).unwrap();
    while puzzle.get_proof_target(&invalid_solution).unwrap() >= minimum_proof_target {
        invalid_solution = puzzle.prove(latest_epoch_hash, address, rng.gen(), None).unwrap();
    }

    // Create a valid transaction for the block.
    let inputs = [Value::from_str(&format!("{address}")).unwrap(), Value::from_str("10u64").unwrap()];
    let transfer_transaction = ledger
        .vm
        .execute(&private_key, ("credits.aleo", "transfer_public"), inputs.iter(), None, 0, None, rng)
        .unwrap();

    // Create a block.
    let block = ledger
        .prepare_advance_to_next_beacon_block(
            &private_key,
            vec![],
            vec![invalid_solution],
            vec![transfer_transaction],
            rng,
        )
        .unwrap();

    // Check that the next block is valid.
    ledger.check_next_block(&block, rng).unwrap();

    // Add the deployment block to the ledger.
    ledger.advance_to_next_block(&block).unwrap();

    // Enforce that the block solution was aborted properly.
    assert!(block.solutions().is_empty());
    assert_eq!(block.aborted_solution_ids(), &vec![invalid_solution.id()]);
}

#[test]
fn test_execute_duplicate_input_ids() {
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

    // Prepare a transfer that spends the record.
    let inputs = [
        Value::Record(record_1.clone()),
        Value::from_str(&format!("{address}")).unwrap(),
        Value::from_str("100u64").unwrap(),
    ];
    let transfer_1 = ledger
        .vm
        .execute(&private_key, ("credits.aleo", "transfer_private"), inputs.into_iter(), None, 0, None, rng)
        .unwrap();
    let transfer_1_id = transfer_1.id();

    // Prepare a transfer that attempts to spend the same record.
    let inputs = [
        Value::Record(record_1.clone()),
        Value::from_str(&format!("{address}")).unwrap(),
        Value::from_str("1000u64").unwrap(),
    ];
    let transfer_2 = ledger
        .vm
        .execute(&private_key, ("credits.aleo", "transfer_private"), inputs.into_iter(), None, 0, None, rng)
        .unwrap();
    let transfer_2_id = transfer_2.id();

    // Prepare a transfer that attempts to spend the same record in the fee.
    let inputs = [Value::from_str(&format!("{address}")).unwrap(), Value::from_str("100u64").unwrap()];
    let transfer_3 = ledger
        .vm
        .execute(
            &private_key,
            ("credits.aleo", "transfer_public"),
            inputs.into_iter(),
            Some(record_1.clone()),
            0,
            None,
            rng,
        )
        .unwrap();
    let transfer_3_id = transfer_3.id();

    // Prepare a transfer that attempts to spend the same record for the subsequent block.
    let inputs =
        [Value::Record(record_1), Value::from_str(&format!("{address}")).unwrap(), Value::from_str("1000u64").unwrap()];
    let transfer_4 = ledger
        .vm
        .execute(&private_key, ("credits.aleo", "transfer_private"), inputs.into_iter(), None, 0, None, rng)
        .unwrap();
    let transfer_4_id = transfer_4.id();

    // Create a block.
    let block = ledger
        .prepare_advance_to_next_beacon_block(
            &private_key,
            vec![],
            vec![],
            vec![transfer_1, transfer_2, transfer_3],
            rng,
        )
        .unwrap();

    // Check that the next block is valid.
    ledger.check_next_block(&block, rng).unwrap();

    // Add the block to the ledger.
    ledger.advance_to_next_block(&block).unwrap();

    // Enforce that the block transactions were correct.
    assert_eq!(block.transactions().num_accepted(), 1);
    assert_eq!(block.transactions().transaction_ids().collect::<Vec<_>>(), vec![&transfer_1_id]);
    assert_eq!(block.aborted_transaction_ids(), &vec![transfer_2_id, transfer_3_id]);

    // Prepare a transfer that will succeed for the subsequent block.
    let inputs = [Value::from_str(&format!("{address}")).unwrap(), Value::from_str("1000u64").unwrap()];
    let transfer_5 = ledger
        .vm
        .execute(&private_key, ("credits.aleo", "transfer_public"), inputs.into_iter(), None, 0, None, rng)
        .unwrap();
    let transfer_5_id = transfer_5.id();

    // Create a block.
    let block = ledger
        .prepare_advance_to_next_beacon_block(&private_key, vec![], vec![], vec![transfer_4, transfer_5], rng)
        .unwrap();

    // Check that the next block is valid.
    ledger.check_next_block(&block, rng).unwrap();

    // Add the block to the ledger.
    ledger.advance_to_next_block(&block).unwrap();

    // Enforce that the block transactions were correct.
    assert_eq!(block.transactions().num_accepted(), 1);
    assert_eq!(block.transactions().transaction_ids().collect::<Vec<_>>(), vec![&transfer_5_id]);
    assert_eq!(block.aborted_transaction_ids(), &vec![transfer_4_id]);
}

#[test]
fn test_execute_duplicate_output_ids() {
    let rng = &mut TestRng::default();

    // Initialize the test environment.
    let crate::test_helpers::TestEnv { ledger, private_key, address, .. } = crate::test_helpers::sample_test_env(rng);

    // Deploy a test program to the ledger.
    let program = Program::<CurrentNetwork>::from_str(
        "
program dummy_program.aleo;

record dummy_program:
    owner as address.private;
    rand_var as u64.private;

function create_duplicate_record:
    input r0 as u64.private;
    cast self.caller 1u64 into r1 as dummy_program.record;
    output r1 as dummy_program.record;",
    )
    .unwrap();

    // Deploy.
    let deployment_transaction = ledger.vm.deploy(&private_key, &program, None, 0, None, rng).unwrap();
    // Verify.
    ledger.vm().check_transaction(&deployment_transaction, None, rng).unwrap();

    // Construct the next block.
    let block = ledger
        .prepare_advance_to_next_beacon_block(&private_key, vec![], vec![], vec![deployment_transaction], rng)
        .unwrap();

    // Check that the next block is valid.
    ledger.check_next_block(&block, rng).unwrap();
    // Add the block to the ledger.
    ledger.advance_to_next_block(&block).unwrap();

    // Create a transaction with different transition ids, but with a fixed output record (output ID).
    let mut create_transaction_with_duplicate_output_id = |x: u64| -> Transaction<CurrentNetwork> {
        // Use a fixed seed RNG.
        let fixed_rng = &mut TestRng::from_seed(1);

        // Create a transaction with a fixed rng.
        let inputs = [Value::from_str(&format!("{x}u64")).unwrap()];
        let transaction = ledger
            .vm
            .execute(
                &private_key,
                ("dummy_program.aleo", "create_duplicate_record"),
                inputs.into_iter(),
                None,
                0,
                None,
                fixed_rng,
            )
            .unwrap();
        // Extract the execution.
        let execution = transaction.execution().unwrap().clone();

        // Create a new fee for the execution.
        let fee_authorization = ledger
            .vm
            .authorize_fee_public(
                &private_key,
                *transaction.fee_amount().unwrap(),
                0,
                execution.to_execution_id().unwrap(),
                rng,
            )
            .unwrap();
        let fee = ledger.vm.execute_fee_authorization(fee_authorization, None, rng).unwrap();

        Transaction::from_execution(execution, Some(fee)).unwrap()
    };

    // Create the first transfer.
    let transfer_1 = create_transaction_with_duplicate_output_id(1);
    let transfer_1_id = transfer_1.id();

    // Create a second transfer with the same output id.
    let transfer_2 = create_transaction_with_duplicate_output_id(2);
    let transfer_2_id = transfer_2.id();

    // Create a third transfer with the same output id.
    let transfer_3 = create_transaction_with_duplicate_output_id(3);
    let transfer_3_id = transfer_3.id();

    // Ensure that each transaction has a duplicate output id.
    let tx_1_output_id = transfer_1.output_ids().next().unwrap();
    let tx_2_output_id = transfer_2.output_ids().next().unwrap();
    let tx_3_output_id = transfer_3.output_ids().next().unwrap();
    assert_eq!(tx_1_output_id, tx_2_output_id);
    assert_eq!(tx_1_output_id, tx_3_output_id);

    // Create a block.
    let block = ledger
        .prepare_advance_to_next_beacon_block(&private_key, vec![], vec![], vec![transfer_1, transfer_2], rng)
        .unwrap();

    // Check that the next block is valid.
    ledger.check_next_block(&block, rng).unwrap();

    // Add the block to the ledger.
    ledger.advance_to_next_block(&block).unwrap();

    // Enforce that the block transactions were correct.
    assert_eq!(block.transactions().num_accepted(), 1);
    assert_eq!(block.transactions().transaction_ids().collect::<Vec<_>>(), vec![&transfer_1_id]);
    assert_eq!(block.aborted_transaction_ids(), &vec![transfer_2_id]);

    // Prepare a transfer that will succeed for the subsequent block.
    let inputs = [Value::from_str(&format!("{address}")).unwrap(), Value::from_str("1000u64").unwrap()];
    let transfer_4 = ledger
        .vm
        .execute(&private_key, ("credits.aleo", "transfer_public"), inputs.into_iter(), None, 0, None, rng)
        .unwrap();
    let transfer_4_id = transfer_4.id();

    // Create a block.
    let block = ledger
        .prepare_advance_to_next_beacon_block(&private_key, vec![], vec![], vec![transfer_3, transfer_4], rng)
        .unwrap();

    // Check that the next block is valid.
    ledger.check_next_block(&block, rng).unwrap();

    // Add the block to the ledger.
    ledger.advance_to_next_block(&block).unwrap();

    // Enforce that the block transactions were correct.
    assert_eq!(block.transactions().num_accepted(), 1);
    assert_eq!(block.transactions().transaction_ids().collect::<Vec<_>>(), vec![&transfer_4_id]);
    assert_eq!(block.aborted_transaction_ids(), &vec![transfer_3_id]);
}

#[test]
fn test_execute_duplicate_transition_ids() {
    let rng = &mut TestRng::default();

    // Initialize the test environment.
    let crate::test_helpers::TestEnv { ledger, private_key, address, .. } = crate::test_helpers::sample_test_env(rng);

    // Deploy a test program to the ledger.
    let program = Program::<CurrentNetwork>::from_str(
        "
program dummy_program.aleo;

function empty_function:
    ",
    )
    .unwrap();

    // Deploy.
    let deployment_transaction = ledger.vm.deploy(&private_key, &program, None, 0, None, rng).unwrap();
    // Verify.
    ledger.vm().check_transaction(&deployment_transaction, None, rng).unwrap();

    // Construct the next block.
    let block = ledger
        .prepare_advance_to_next_beacon_block(&private_key, vec![], vec![], vec![deployment_transaction], rng)
        .unwrap();

    // Check that the next block is valid.
    ledger.check_next_block(&block, rng).unwrap();
    // Add the block to the ledger.
    ledger.advance_to_next_block(&block).unwrap();

    // Create a transaction with different transaction IDs, but with a fixed transition ID.
    let mut create_transaction_with_duplicate_transition_id = || -> Transaction<CurrentNetwork> {
        // Use a fixed seed RNG.
        let fixed_rng = &mut TestRng::from_seed(1);

        // Create a transaction with a fixed rng.
        let inputs: [Value<_>; 0] = [];
        let transaction = ledger
            .vm
            .execute(
                &private_key,
                ("dummy_program.aleo", "empty_function"),
                inputs.into_iter(),
                None,
                0,
                None,
                fixed_rng,
            )
            .unwrap();
        // Extract the execution.
        let execution = transaction.execution().unwrap().clone();

        // Create a new fee for the execution.
        let fee_authorization = ledger
            .vm
            .authorize_fee_public(
                &private_key,
                *transaction.fee_amount().unwrap(),
                0,
                execution.to_execution_id().unwrap(),
                rng,
            )
            .unwrap();
        let fee = ledger.vm.execute_fee_authorization(fee_authorization, None, rng).unwrap();

        Transaction::from_execution(execution, Some(fee)).unwrap()
    };

    // Create the first transaction.
    let transaction_1 = create_transaction_with_duplicate_transition_id();
    let transaction_1_id = transaction_1.id();

    // Create a second transaction with the same transition id.
    let transaction_2 = create_transaction_with_duplicate_transition_id();
    let transaction_2_id = transaction_2.id();

    // Create a third transaction with the same transition_id
    let transaction_3 = create_transaction_with_duplicate_transition_id();
    let transaction_3_id = transaction_3.id();

    // Ensure that each transaction has a duplicate transition id.
    let tx_1_transition_id = transaction_1.transition_ids().next().unwrap();
    let tx_2_transition_id = transaction_2.transition_ids().next().unwrap();
    let tx_3_transition_id = transaction_3.transition_ids().next().unwrap();
    assert_eq!(tx_1_transition_id, tx_2_transition_id);
    assert_eq!(tx_1_transition_id, tx_3_transition_id);

    // Create a block.
    let block = ledger
        .prepare_advance_to_next_beacon_block(&private_key, vec![], vec![], vec![transaction_1, transaction_2], rng)
        .unwrap();

    // Check that the next block is valid.
    ledger.check_next_block(&block, rng).unwrap();

    // Add the block to the ledger.
    ledger.advance_to_next_block(&block).unwrap();

    // Enforce that the block transactions were correct.
    assert_eq!(block.transactions().num_accepted(), 1);
    assert_eq!(block.transactions().transaction_ids().collect::<Vec<_>>(), vec![&transaction_1_id]);
    assert_eq!(block.aborted_transaction_ids(), &vec![transaction_2_id]);

    // Prepare a transfer that will succeed for the subsequent block.
    let inputs = [Value::from_str(&format!("{address}")).unwrap(), Value::from_str("1000u64").unwrap()];
    let transfer_transaction = ledger
        .vm
        .execute(&private_key, ("credits.aleo", "transfer_public"), inputs.into_iter(), None, 0, None, rng)
        .unwrap();
    let transfer_transaction_id = transfer_transaction.id();

    // Create a block.
    let block = ledger
        .prepare_advance_to_next_beacon_block(
            &private_key,
            vec![],
            vec![],
            vec![transaction_3, transfer_transaction],
            rng,
        )
        .unwrap();

    // Check that the next block is valid.
    ledger.check_next_block(&block, rng).unwrap();

    // Add the block to the ledger.
    ledger.advance_to_next_block(&block).unwrap();

    // Enforce that the block transactions were correct.
    assert_eq!(block.transactions().num_accepted(), 1);
    assert_eq!(block.transactions().transaction_ids().collect::<Vec<_>>(), vec![&transfer_transaction_id]);
    assert_eq!(block.aborted_transaction_ids(), &vec![transaction_3_id]);
}

#[test]
fn test_execute_duplicate_transition_public_keys() {
    let rng = &mut TestRng::default();

    // Initialize the test environment.
    let crate::test_helpers::TestEnv { ledger, private_key, address, .. } = crate::test_helpers::sample_test_env(rng);

    // Deploy a test program to the ledger.
    let program = Program::<CurrentNetwork>::from_str(
        "
program dummy_program.aleo;

function empty_function:

function simple_output:
    output 1u64 as u64.public;
    ",
    )
    .unwrap();

    // Deploy.
    let deployment_transaction = ledger.vm.deploy(&private_key, &program, None, 0, None, rng).unwrap();
    // Verify.
    ledger.vm().check_transaction(&deployment_transaction, None, rng).unwrap();

    // Construct the next block.
    let block = ledger
        .prepare_advance_to_next_beacon_block(&private_key, vec![], vec![], vec![deployment_transaction], rng)
        .unwrap();

    // Check that the next block is valid.
    ledger.check_next_block(&block, rng).unwrap();
    // Add the block to the ledger.
    ledger.advance_to_next_block(&block).unwrap();

    // Create a transaction with different transaction ids, but with a TPK.
    let mut create_transaction_with_duplicate_tpk = |function: &str| -> Transaction<CurrentNetwork> {
        // Use a fixed seed RNG.
        let fixed_rng = &mut TestRng::from_seed(1);

        // Create a transaction with a fixed rng.
        let inputs: [Value<_>; 0] = [];
        let transaction = ledger
            .vm
            .execute(&private_key, ("dummy_program.aleo", function), inputs.into_iter(), None, 0, None, fixed_rng)
            .unwrap();
        // Extract the execution.
        let execution = transaction.execution().unwrap().clone();

        // Create a new fee for the execution.
        let fee_authorization = ledger
            .vm
            .authorize_fee_public(
                &private_key,
                *transaction.fee_amount().unwrap(),
                0,
                execution.to_execution_id().unwrap(),
                rng,
            )
            .unwrap();
        let fee = ledger.vm.execute_fee_authorization(fee_authorization, None, rng).unwrap();

        Transaction::from_execution(execution, Some(fee)).unwrap()
    };

    // Create the first transaction.
    let transaction_1 = create_transaction_with_duplicate_tpk("empty_function");
    let transaction_1_id = transaction_1.id();

    // Create a second transaction with the same tpk and tcm.
    let transaction_2 = create_transaction_with_duplicate_tpk("simple_output");
    let transaction_2_id = transaction_2.id();

    // Create a third transaction with the same tpk and tcm.
    let transaction_3 = create_transaction_with_duplicate_tpk("simple_output");
    let transaction_3_id = transaction_3.id();

    // Ensure that each transaction has a duplicate tcm and tpk.
    let tx_1_tpk = transaction_1.transitions().next().unwrap().tpk();
    let tx_2_tpk = transaction_2.transitions().next().unwrap().tpk();
    let tx_3_tpk = transaction_3.transitions().next().unwrap().tpk();
    assert_eq!(tx_1_tpk, tx_2_tpk);
    assert_eq!(tx_1_tpk, tx_3_tpk);

    let tx_1_tcm = transaction_1.transitions().next().unwrap().tcm();
    let tx_2_tcm = transaction_2.transitions().next().unwrap().tcm();
    let tx_3_tcm = transaction_3.transitions().next().unwrap().tcm();
    assert_eq!(tx_1_tcm, tx_2_tcm);
    assert_eq!(tx_1_tcm, tx_3_tcm);

    // Create a block.
    let block = ledger
        .prepare_advance_to_next_beacon_block(&private_key, vec![], vec![], vec![transaction_1, transaction_2], rng)
        .unwrap();

    // Check that the next block is valid.
    ledger.check_next_block(&block, rng).unwrap();

    // Add the block to the ledger.
    ledger.advance_to_next_block(&block).unwrap();

    // Enforce that the block transactions were correct.
    assert_eq!(block.transactions().num_accepted(), 1);
    assert_eq!(block.transactions().transaction_ids().collect::<Vec<_>>(), vec![&transaction_1_id]);
    assert_eq!(block.aborted_transaction_ids(), &vec![transaction_2_id]);

    // Prepare a transfer that will succeed for the subsequent block.
    let inputs = [Value::from_str(&format!("{address}")).unwrap(), Value::from_str("1000u64").unwrap()];
    let transfer_transaction = ledger
        .vm
        .execute(&private_key, ("credits.aleo", "transfer_public"), inputs.into_iter(), None, 0, None, rng)
        .unwrap();
    let transfer_transaction_id = transfer_transaction.id();

    // Create a block.
    let block = ledger
        .prepare_advance_to_next_beacon_block(
            &private_key,
            vec![],
            vec![],
            vec![transaction_3, transfer_transaction],
            rng,
        )
        .unwrap();

    // Check that the next block is valid.
    ledger.check_next_block(&block, rng).unwrap();

    // Add the block to the ledger.
    ledger.advance_to_next_block(&block).unwrap();

    // Enforce that the block transactions were correct.
    assert_eq!(block.transactions().num_accepted(), 1);
    assert_eq!(block.transactions().transaction_ids().collect::<Vec<_>>(), vec![&transfer_transaction_id]);
    assert_eq!(block.aborted_transaction_ids(), &vec![transaction_3_id]);
}

#[test]
fn test_abort_fee_transaction() {
    let rng = &mut TestRng::default();

    // Initialize the test environment.
    let crate::test_helpers::TestEnv { ledger, private_key, address, .. } = crate::test_helpers::sample_test_env(rng);

    // Construct valid transaction for the ledger.
    let inputs = [Value::from_str(&format!("{address}")).unwrap(), Value::from_str("1000u64").unwrap()];
    let transaction = ledger
        .vm
        .execute(&private_key, ("credits.aleo", "transfer_public"), inputs.clone().into_iter(), None, 0, None, rng)
        .unwrap();
    let transaction_id = transaction.id();

    // Convert a fee transaction.
    let transaction_to_convert_to_fee = ledger
        .vm
        .execute(&private_key, ("credits.aleo", "transfer_public"), inputs.into_iter(), None, 0, None, rng)
        .unwrap();
    let fee_transaction = Transaction::from_fee(transaction_to_convert_to_fee.fee_transition().unwrap()).unwrap();
    let fee_transaction_id = fee_transaction.id();

    // Create a block using a fee transaction.
    let block = ledger
        .prepare_advance_to_next_beacon_block(&private_key, vec![], vec![], vec![fee_transaction, transaction], rng)
        .unwrap();

    // Check that the block aborts the invalid transaction.
    assert_eq!(block.aborted_transaction_ids(), &vec![fee_transaction_id]);
    assert_eq!(block.transaction_ids().collect::<Vec<_>>(), vec![&transaction_id]);

    // Check that the next block is valid.
    ledger.check_next_block(&block, rng).unwrap();

    // Add the block to the ledger.
    ledger.advance_to_next_block(&block).unwrap();
}

#[test]
fn test_abort_invalid_transaction() {
    let rng = &mut TestRng::default();

    // Initialize the test environment.
    let crate::test_helpers::TestEnv { ledger, private_key, address, .. } = crate::test_helpers::sample_test_env(rng);

    // Initialize a new VM.
    let vm = VM::from(ConsensusStore::<CurrentNetwork, ConsensusMemory<CurrentNetwork>>::open(None).unwrap()).unwrap();

    // Construct a custom genesis block.
    let custom_genesis = vm.genesis_beacon(&private_key, rng).unwrap();

    // Update the VM.
    vm.add_next_block(&custom_genesis).unwrap();

    // Generate a transaction that will be invalid on another network.
    let inputs = [Value::from_str(&format!("{address}")).unwrap(), Value::from_str("1000u64").unwrap()];
    let invalid_transaction = vm
        .execute(&private_key, ("credits.aleo", "transfer_public"), inputs.clone().into_iter(), None, 0, None, rng)
        .unwrap();
    let invalid_transaction_id = invalid_transaction.id();

    // Check that the ledger deems this transaction invalid.
    assert!(ledger.check_transaction_basic(&invalid_transaction, None, rng).is_err());

    // Construct valid transactions for the ledger.
    let valid_transaction_1 = ledger
        .vm
        .execute(&private_key, ("credits.aleo", "transfer_public"), inputs.clone().into_iter(), None, 0, None, rng)
        .unwrap();
    let valid_transaction_2 = ledger
        .vm
        .execute(&private_key, ("credits.aleo", "transfer_public"), inputs.into_iter(), None, 0, None, rng)
        .unwrap();
    let valid_transaction_id_1 = valid_transaction_1.id();
    let valid_transaction_id_2 = valid_transaction_2.id();

    // Create a block.
    let block = ledger
        .prepare_advance_to_next_beacon_block(
            &private_key,
            vec![],
            vec![],
            vec![valid_transaction_1, invalid_transaction, valid_transaction_2],
            rng,
        )
        .unwrap();

    // Check that the block aborts the invalid transaction.
    assert_eq!(block.aborted_transaction_ids(), &vec![invalid_transaction_id]);
    assert_eq!(block.transaction_ids().collect::<Vec<_>>(), vec![&valid_transaction_id_1, &valid_transaction_id_2]);

    // Check that the next block is valid.
    ledger.check_next_block(&block, rng).unwrap();

    // Add the block to the ledger.
    ledger.advance_to_next_block(&block).unwrap();
}

#[test]
fn test_deployment_duplicate_program_id() {
    let rng = &mut TestRng::default();

    // Initialize the test environment.
    let crate::test_helpers::TestEnv { ledger, private_key, .. } = crate::test_helpers::sample_test_env(rng);

    // Create two programs with a duplicate program ID but different mappings
    let program_1 = Program::<CurrentNetwork>::from_str(
        r"
program dummy_program.aleo;
mapping abcd1:
    key as address.public;
    value as u64.public;
function foo:
    input r0 as u8.private;
    async foo r0 into r1;
    output r1 as dummy_program.aleo/foo.future;
finalize foo:
    input r0 as u8.public;
    add r0 r0 into r1;",
    )
    .unwrap();

    let program_2 = Program::<CurrentNetwork>::from_str(
        r"
program dummy_program.aleo;
mapping abcd2:
    key as address.public;
    value as u64.public;
function foo2:
    input r0 as u8.private;
    async foo2 r0 into r1;
    output r1 as dummy_program.aleo/foo2.future;
finalize foo2:
    input r0 as u8.public;
    add r0 r0 into r1;",
    )
    .unwrap();

    // Create a deployment transaction for the first program.
    let deployment_1 = ledger.vm.deploy(&private_key, &program_1, None, 0, None, rng).unwrap();
    let deployment_1_id = deployment_1.id();
    assert!(ledger.check_transaction_basic(&deployment_1, None, rng).is_ok());

    // Create a deployment transaction for the second program.
    let deployment_2 = ledger.vm.deploy(&private_key, &program_2, None, 0, None, rng).unwrap();
    let deployment_2_id = deployment_2.id();
    assert!(ledger.check_transaction_basic(&deployment_2, None, rng).is_ok());

    // Create a block.
    let block = ledger
        .prepare_advance_to_next_beacon_block(&private_key, vec![], vec![], vec![deployment_1, deployment_2], rng)
        .unwrap();

    // Check that the next block is valid.
    ledger.check_next_block(&block, rng).unwrap();

    // Add the block to the ledger.
    ledger.advance_to_next_block(&block).unwrap();

    // Enforce that the block transactions were correct.
    assert_eq!(block.transactions().num_accepted(), 1);
    assert_eq!(block.transactions().num_rejected(), 1);

    // Enforce that the first program was deployed and the second was rejected.
    assert_eq!(ledger.get_program(*program_1.id()).unwrap(), program_1);
    assert!(ledger.vm.transaction_store().contains_transaction_id(&deployment_1_id).unwrap());
    assert!(ledger.vm.block_store().contains_rejected_or_aborted_transaction_id(&deployment_2_id).unwrap());
}

#[test]
fn test_split_candidate_solutions() {
    let rng = &mut TestRng::default();

    let max_solutions = CurrentNetwork::MAX_SOLUTIONS;

    const ITERATIONS: usize = 1_000;

    for _ in 0..ITERATIONS {
        let num_candidates = rng.gen_range(0..max_solutions * 2);
        let candidate_solutions: Vec<u8> = rng.sample_iter(Standard).take(num_candidates).collect();

        let (_accepted, _aborted) =
            split_candidate_solutions(candidate_solutions, max_solutions, |candidate| candidate % 2 == 0);
    }
}

#[test]
fn test_max_committee_limit_with_bonds() {
    // Initialize an RNG.
    let rng = &mut TestRng::default();

    // Initialize the VM.
    let vm = VM::from(ConsensusStore::<CurrentNetwork, ConsensusMemory<CurrentNetwork>>::open(None).unwrap()).unwrap();

    // Construct the validators, one less than the maximum committee size.
    let validators = (0..Committee::<CurrentNetwork>::MAX_COMMITTEE_SIZE - 1)
        .map(|_| {
            let private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
            let amount = MIN_VALIDATOR_STAKE;
            let is_open = true;
            (private_key, (amount, is_open))
        })
        .collect::<IndexMap<_, _>>();

    // Track the allocated amount.
    let mut allocated_amount = 0;

    // Construct the committee.
    let mut committee_map = IndexMap::new();
    for (private_key, (amount, _)) in &validators {
        let address = Address::try_from(private_key).unwrap();
        committee_map.insert(address, (*amount, true));
        allocated_amount += *amount;
    }

    // Initialize two new validators.
    let first_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
    let first_address = Address::try_from(&first_private_key).unwrap();
    let second_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
    let second_address = Address::try_from(&second_private_key).unwrap();

    // Construct the public balances, allocating the remaining supply to the first validator and two new validators.
    // The remaining validators will have a balance of 0.
    let mut public_balances = IndexMap::new();
    for (private_key, _) in &validators {
        public_balances.insert(Address::try_from(private_key).unwrap(), 0);
    }
    let remaining_supply = <CurrentNetwork as Network>::STARTING_SUPPLY - allocated_amount;
    let amount = remaining_supply / 3;
    public_balances.insert(Address::try_from(validators.keys().next().unwrap()).unwrap(), amount);
    public_balances.insert(first_address, amount);
    public_balances.insert(second_address, remaining_supply - 2 * amount);

    // Construct the bonded balances.
    let bonded_balances = validators
        .iter()
        .map(|(private_key, (amount, _))| {
            let address = Address::try_from(private_key).unwrap();
            (address, (address, address, *amount))
        })
        .collect();

    // Construct the genesis block, which should pass.
    let genesis_block = vm
        .genesis_quorum(
            validators.keys().next().unwrap(),
            Committee::new_genesis(committee_map).unwrap(),
            public_balances,
            bonded_balances,
            rng,
        )
        .unwrap();

    // Initialize a Ledger from the genesis block.
    let ledger =
        Ledger::<CurrentNetwork, ConsensusMemory<CurrentNetwork>>::load(genesis_block, StorageMode::Production)
            .unwrap();

    // Bond the first validator.
    let bond_first_transaction = ledger
        .vm()
        .execute(
            &first_private_key,
            ("credits.aleo", "bond_public"),
            vec![
                Value::<CurrentNetwork>::from_str(&first_address.to_string()).unwrap(),
                Value::<CurrentNetwork>::from_str(&first_address.to_string()).unwrap(),
                Value::<CurrentNetwork>::from_str(&format!("{MIN_VALIDATOR_STAKE}u64")).unwrap(),
            ]
            .iter(),
            None,
            0,
            None,
            rng,
        )
        .unwrap();

    // Create a block.
    let block = ledger
        .prepare_advance_to_next_beacon_block(
            validators.keys().next().unwrap(),
            vec![],
            vec![],
            vec![bond_first_transaction],
            rng,
        )
        .unwrap();

    // Check that the next block is valid.
    ledger.check_next_block(&block, rng).unwrap();

    // Check that the first validator is not in the committee.
    let committee = ledger.latest_committee().unwrap();
    assert!(!committee.is_committee_member(first_address));

    // Add the block to the ledger.
    ledger.advance_to_next_block(&block).unwrap();

    // Check that the first validator was added to the committee.
    let committee = ledger.latest_committee().unwrap();
    assert!(committee.is_committee_member(first_address));

    // Attempt to bond the second validator.
    let bond_second_transaction = ledger
        .vm()
        .execute(
            &second_private_key,
            ("credits.aleo", "bond_public"),
            vec![
                Value::<CurrentNetwork>::from_str(&second_address.to_string()).unwrap(),
                Value::<CurrentNetwork>::from_str(&second_address.to_string()).unwrap(),
                Value::<CurrentNetwork>::from_str(&format!("{MIN_VALIDATOR_STAKE}u64")).unwrap(),
            ]
            .iter(),
            None,
            0,
            None,
            rng,
        )
        .unwrap();

    // Create a block.
    let block = ledger
        .prepare_advance_to_next_beacon_block(
            validators.keys().next().unwrap(),
            vec![],
            vec![],
            vec![bond_second_transaction],
            rng,
        )
        .unwrap();

    // Ensure that the `bond_second_transaction` is rejected.
    assert_eq!(block.transactions().num_rejected(), 1);

    // Check that the next block is valid.
    ledger.check_next_block(&block, rng).unwrap();

    // Check that the second validator is not in the committee.
    let committee = ledger.latest_committee().unwrap();
    assert!(!committee.is_committee_member(second_address));

    // Add the block to the ledger.
    ledger.advance_to_next_block(&block).unwrap();

    // Check that the second validator was not added to the committee.
    let committee = ledger.latest_committee().unwrap();
    assert!(!committee.is_committee_member(second_address));
}

#[test]
fn test_deployment_exceeding_max_transaction_spend() {
    let rng = &mut TestRng::default();

    // Initialize the test environment.
    let crate::test_helpers::TestEnv { ledger, private_key, .. } = crate::test_helpers::sample_test_env(rng);

    // Construct two programs, one that is allowed and one that exceeds the maximum transaction spend.
    let mut allowed_program = None;
    let mut exceeding_program = None;

    for i in 0..<CurrentNetwork as Network>::MAX_COMMANDS.ilog2() {
        // Construct the finalize body.
        let finalize_body =
            (0..2.pow(i)).map(|i| format!("hash.bhp256 0field into r{i} as field;")).collect::<Vec<_>>().join("\n");

        // Construct the program.
        let program = Program::from_str(&format!(
            r"program test_max_spend_limit_{i}.aleo;
          function foo:
          async foo into r0;
          output r0 as test_max_spend_limit_{i}.aleo/foo.future;

          finalize foo:{finalize_body}",
        ))
        .unwrap();

        // Attempt to initialize a `Stack` for the program.
        // If this fails, then by `Stack::initialize` the finalize cost exceeds the `TRANSACTION_SPEND_LIMIT`.
        if Stack::<CurrentNetwork>::new(&ledger.vm().process().read(), &program).is_err() {
            exceeding_program = Some(program);
            break;
        } else {
            allowed_program = Some(program);
        }
    }

    // Ensure that the allowed and exceeding programs are not None.
    assert!(allowed_program.is_some());
    assert!(exceeding_program.is_some());

    let allowed_program = allowed_program.unwrap();
    let exceeding_program = exceeding_program.unwrap();

    // Deploy the allowed program.
    let deployment = ledger.vm().deploy(&private_key, &allowed_program, None, 0, None, rng).unwrap();

    // Verify the deployment transaction.
    assert!(ledger.vm().check_transaction(&deployment, None, rng).is_ok());

    // Construct the next block.
    let block =
        ledger.prepare_advance_to_next_beacon_block(&private_key, vec![], vec![], vec![deployment], rng).unwrap();

    // Check that the next block is valid.
    ledger.check_next_block(&block, rng).unwrap();

    // Add the block to the ledger.
    ledger.advance_to_next_block(&block).unwrap();

    // Check that the program exists in the VM.
    assert!(ledger.vm().contains_program(allowed_program.id()));

    // Attempt to deploy the exceeding program.
    let result = ledger.vm().deploy(&private_key, &exceeding_program, None, 0, None, rng);

    // Check that the deployment failed.
    assert!(result.is_err());
}

// These tests require the proof targets to be low enough to be able to generate **valid** solutions.
// This requires the 'test' feature to be enabled for the `console` dependency.
#[cfg(feature = "test")]
mod valid_solutions {
    use super::*;
    use rand::prelude::SliceRandom;
    use std::collections::HashSet;

    #[test]
    fn test_duplicate_solution_ids() {
        // Print the cfg to ensure that the test is running in the correct environment.
        let rng = &mut TestRng::default();

        // Initialize the test environment.
        let crate::test_helpers::TestEnv { ledger, private_key, address, .. } =
            crate::test_helpers::sample_test_env(rng);

        // Retrieve the puzzle parameters.
        let puzzle = ledger.puzzle();
        let latest_epoch_hash = ledger.latest_epoch_hash().unwrap();
        let minimum_proof_target = ledger.latest_proof_target();

        // Create a solution that is greater than the minimum proof target.
        let mut valid_solution = puzzle.prove(latest_epoch_hash, address, rng.gen(), None).unwrap();
        while puzzle.get_proof_target(&valid_solution).unwrap() < minimum_proof_target {
            println!(
                "Solution is invalid: {} < {}",
                puzzle.get_proof_target(&valid_solution).unwrap(),
                minimum_proof_target
            );
            valid_solution = puzzle.prove(latest_epoch_hash, address, rng.gen(), None).unwrap();
        }

        // Create a valid transaction for the block.
        let inputs = [Value::from_str(&format!("{address}")).unwrap(), Value::from_str("10u64").unwrap()];
        let transfer_transaction = ledger
            .vm
            .execute(&private_key, ("credits.aleo", "transfer_public"), inputs.iter(), None, 0, None, rng)
            .unwrap();

        // Check that block creation fails when duplicate solution IDs are provided.
        let result = ledger.prepare_advance_to_next_beacon_block(
            &private_key,
            vec![],
            vec![valid_solution, valid_solution],
            vec![transfer_transaction.clone()],
            rng,
        );
        assert!(result.is_err());

        // Create a block.
        let block = ledger
            .prepare_advance_to_next_beacon_block(
                &private_key,
                vec![],
                vec![valid_solution],
                vec![transfer_transaction],
                rng,
            )
            .unwrap();

        // Check that the next block is valid.
        ledger.check_next_block(&block, rng).unwrap();

        // Add the deployment block to the ledger.
        ledger.advance_to_next_block(&block).unwrap();

        // Enforce that the block solution was accepted properly.
        assert_eq!(block.solutions().len(), 1);
        assert_eq!(block.aborted_solution_ids().len(), 0)
    }

    #[test]
    fn test_excess_invalid_solution_ids() {
        // Note that the sum of `NUM_INVALID_SOLUTIONS` and `NUM_VALID_SOLUTIONS` should exceed the maximum number of solutions.
        const NUM_INVALID_SOLUTIONS: usize = CurrentNetwork::MAX_SOLUTIONS;
        const NUM_VALID_SOLUTIONS: usize = CurrentNetwork::MAX_SOLUTIONS;

        let rng = &mut TestRng::default();

        // Initialize the test environment.
        let crate::test_helpers::TestEnv { ledger, private_key, address, .. } =
            crate::test_helpers::sample_test_env(rng);

        // Retrieve the puzzle parameters.
        let puzzle = ledger.puzzle();
        let latest_epoch_hash = ledger.latest_epoch_hash().unwrap();
        let minimum_proof_target = ledger.latest_proof_target();

        // Initialize storage for the valid and invalid solutions
        let mut valid_solutions = Vec::with_capacity(NUM_VALID_SOLUTIONS);
        let mut invalid_solutions = Vec::with_capacity(NUM_INVALID_SOLUTIONS);

        // Create solutions that are greater than the minimum proof target.
        while valid_solutions.len() < NUM_VALID_SOLUTIONS {
            let solution = puzzle.prove(latest_epoch_hash, address, rng.gen(), None).unwrap();
            if puzzle.get_proof_target(&solution).unwrap() < minimum_proof_target {
                if invalid_solutions.len() < NUM_INVALID_SOLUTIONS {
                    invalid_solutions.push(solution);
                }
            } else {
                valid_solutions.push(solution);
            }
        }
        // Create the remaining solutions that are less than the minimum proof target.
        while invalid_solutions.len() < NUM_INVALID_SOLUTIONS {
            let solution = puzzle.prove(latest_epoch_hash, address, rng.gen(), None).unwrap();
            if puzzle.get_proof_target(&solution).unwrap() < minimum_proof_target {
                invalid_solutions.push(solution);
            }
        }

        // Check the length of the valid and invalid solutions.
        assert_eq!(valid_solutions.len(), NUM_VALID_SOLUTIONS);
        assert_eq!(invalid_solutions.len(), NUM_INVALID_SOLUTIONS);

        // Concatenate and shuffle the solutions.
        let mut candidate_solutions = valid_solutions.clone();
        candidate_solutions.extend(invalid_solutions.clone());
        candidate_solutions.shuffle(rng);

        // Create a valid transaction for the block.
        let inputs = [Value::from_str(&format!("{address}")).unwrap(), Value::from_str("10u64").unwrap()];
        let transfer_transaction = ledger
            .vm
            .execute(&private_key, ("credits.aleo", "transfer_public"), inputs.iter(), None, 0, None, rng)
            .unwrap();

        // Create a block.
        let block = ledger
            .prepare_advance_to_next_beacon_block(
                &private_key,
                vec![],
                candidate_solutions,
                vec![transfer_transaction],
                rng,
            )
            .unwrap();

        // Check that the next block is valid.
        ledger.check_next_block(&block, rng).unwrap();

        // Add the deployment block to the ledger.
        ledger.advance_to_next_block(&block).unwrap();

        // Check that the block's solutions are well-formed.
        assert_eq!(block.aborted_solution_ids().len(), NUM_INVALID_SOLUTIONS);
        assert_eq!(block.solutions().len(), NUM_VALID_SOLUTIONS);

        let block_solutions = block.solutions().solution_ids().cloned().collect::<HashSet<_>>();
        let valid_solutions = valid_solutions.iter().map(|s| s.id()).collect::<HashSet<_>>();
        assert_eq!(block_solutions, valid_solutions, "Valid solutions do not match");

        let block_aborted_solution_ids = block.aborted_solution_ids().iter().cloned().collect::<HashSet<_>>();
        let invalid_solutions = invalid_solutions.iter().map(|s| s.id()).collect::<HashSet<_>>();
        assert_eq!(block_aborted_solution_ids, invalid_solutions, "Invalid solutions do not match");
    }

    #[test]
    fn test_excess_valid_solution_ids() {
        // Note that this should be greater than the maximum number of solutions.
        const NUM_VALID_SOLUTIONS: usize = 2 * CurrentNetwork::MAX_SOLUTIONS;

        let rng = &mut TestRng::default();

        // Initialize the test environment.
        let crate::test_helpers::TestEnv { ledger, private_key, address, .. } =
            crate::test_helpers::sample_test_env(rng);

        // Retrieve the puzzle parameters.
        let puzzle = ledger.puzzle();
        let latest_epoch_hash = ledger.latest_epoch_hash().unwrap();
        let minimum_proof_target = ledger.latest_proof_target();

        // Initialize storage for the valid solutions
        let mut valid_solutions = Vec::with_capacity(NUM_VALID_SOLUTIONS);

        // Create solutions that are greater than the minimum proof target.
        while valid_solutions.len() < NUM_VALID_SOLUTIONS {
            let solution = puzzle.prove(latest_epoch_hash, address, rng.gen(), None).unwrap();
            if puzzle.get_proof_target(&solution).unwrap() >= minimum_proof_target {
                valid_solutions.push(solution);
            }
        }

        // Check the length of the valid solutions.
        assert_eq!(valid_solutions.len(), NUM_VALID_SOLUTIONS);

        // Shuffle the solutions.
        let mut candidate_solutions = valid_solutions;
        candidate_solutions.shuffle(rng);

        // Create a valid transaction for the block.
        let inputs = [Value::from_str(&format!("{address}")).unwrap(), Value::from_str("10u64").unwrap()];
        let transfer_transaction = ledger
            .vm
            .execute(&private_key, ("credits.aleo", "transfer_public"), inputs.iter(), None, 0, None, rng)
            .unwrap();

        // Create a block.
        let block = ledger
            .prepare_advance_to_next_beacon_block(
                &private_key,
                vec![],
                candidate_solutions.clone(),
                vec![transfer_transaction],
                rng,
            )
            .unwrap();

        // Check that the next block is valid.
        ledger.check_next_block(&block, rng).unwrap();

        // Add the deployment block to the ledger.
        ledger.advance_to_next_block(&block).unwrap();

        // Check that the block's solutions are well-formed.
        assert_eq!(block.solutions().len(), CurrentNetwork::MAX_SOLUTIONS);
        assert_eq!(block.aborted_solution_ids().len(), NUM_VALID_SOLUTIONS - CurrentNetwork::MAX_SOLUTIONS);

        let block_solutions = block.solutions().solution_ids().cloned().collect::<HashSet<_>>();
        let expected_accepted_solutions =
            candidate_solutions.iter().take(CurrentNetwork::MAX_SOLUTIONS).map(|s| s.id()).collect::<HashSet<_>>();
        assert_eq!(block_solutions, expected_accepted_solutions, "Accepted solutions do not match");

        let block_aborted_solution_ids = block.aborted_solution_ids().iter().cloned().collect::<HashSet<_>>();
        let expected_aborted_solutions =
            candidate_solutions.iter().skip(CurrentNetwork::MAX_SOLUTIONS).map(|s| s.id()).collect::<HashSet<_>>();
        assert_eq!(block_aborted_solution_ids, expected_aborted_solutions, "Aborted solutions do not match");
    }
}
