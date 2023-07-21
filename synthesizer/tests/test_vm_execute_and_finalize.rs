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

mod utilities;

use indexmap::IndexMap;
use rayon::prelude::*;
use std::borrow::Borrow;
use utilities::*;

use console::{
    account::{PrivateKey, ViewKey},
    network::prelude::*,
    program::{Entry, Identifier, Literal, Plaintext, Record, Value, RATIFICATIONS_DEPTH, U64},
    types::{Boolean, Field},
};
use ledger_block::{Block, ConfirmedTransaction, Header, Metadata, Transaction, Transactions, Transition};
use ledger_store::{helpers::memory::ConsensusMemory, ConsensusStorage, ConsensusStore};
use snarkvm_synthesizer::VM;
use synthesizer_program::FinalizeGlobalState;

#[test]
fn test_vm_execute_and_finalize() {
    // Load the tests.
    let tests = load_tests::<_, ProgramTest>("./tests/program", "./expectations/vm/execute_and_finalize");

    // Run each test and compare it against its corresponding expectation.
    tests.par_iter().for_each(|test| {
        // Initialize the RNG.
        let rng = &mut match test.randomness() {
            None => TestRng::fixed(123456789),
            Some(randomness) => TestRng::fixed(randomness),
        };

        // Initialize a private key.
        let genesis_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();

        // Initialize the VM.
        let (vm, records) = initialize_vm(&genesis_private_key, rng);

        // Pre-construct the necessary fee records.
        let num_fee_records = 1 + test.cases().len();
        let mut fee_records = construct_fee_records(&vm, &genesis_private_key, records, num_fee_records, rng);

        // Deploy the program.
        let transaction =
            vm.deploy(&genesis_private_key, test.program(), (fee_records.pop().unwrap().0, 0), None, rng).unwrap();
        let transactions = vm.speculate(construct_finalize_global_state(&vm), [transaction].iter()).unwrap();
        let block = construct_next_block(&vm, &genesis_private_key, transactions, rng).unwrap();
        vm.add_next_block(&block).unwrap();

        // Run each test case, aggregating the outputs.
        let outputs = test
            .cases()
            .iter()
            .map(|value| {
                // TODO: Dedup from other integration tests.
                // Extract the function name, inputs, and optional private key.
                let value = value.as_mapping().expect("expected mapping for test case");
                let function_name = Identifier::<CurrentNetwork>::from_str(
                    value
                        .get("function")
                        .expect("expected function name for test case")
                        .as_str()
                        .expect("expected string for function name"),
                )
                .expect("unable to parse function name");
                let inputs = value
                    .get("inputs")
                    .expect("expected inputs for test case")
                    .as_sequence()
                    .expect("expected sequence for inputs")
                    .iter()
                    .map(|input| match &input {
                        serde_yaml::Value::Bool(bool) => {
                            Value::<CurrentNetwork>::from(Literal::Boolean(Boolean::new(*bool)))
                        }
                        _ => Value::<CurrentNetwork>::from_str(input.as_str().expect("expected string for input"))
                            .expect("unable to parse input"),
                    })
                    .collect_vec();
                // TODO: Support fee records for custom private keys.
                let private_key = match value.get("private_key") {
                    Some(private_key) => PrivateKey::<CurrentNetwork>::from_str(
                        private_key.as_str().expect("expected string for private key"),
                    )
                    .expect("unable to parse private key"),
                    None => genesis_private_key,
                };

                // A helper function to run the test and extract the outputs as YAML, to be compared against the expectation.
                let mut run_test = || -> serde_yaml::Value {
                    // Create a mapping to store the output.
                    let mut output = serde_yaml::Mapping::new();
                    // Execute the function, extracting the transaction.
                    let transaction = match vm.execute(
                        &private_key,
                        (test.program().id(), function_name),
                        inputs.iter(),
                        Some((fee_records.pop().unwrap().0, 0u64)),
                        None,
                        rng,
                    ) {
                        Ok(transaction) => transaction,
                        // If the execution fails, return the error.
                        Err(err) => {
                            output.insert(
                                serde_yaml::Value::String("execute".to_string()),
                                serde_yaml::Value::String(err.to_string()),
                            );
                            return serde_yaml::Value::Mapping(output);
                        }
                    };
                    // For each transition in the transaction, extract the transition outputs and the inputs for finalize.
                    let mut execute = serde_yaml::Mapping::new();
                    for transition in transaction.transitions() {
                        let mut transition_output = serde_yaml::Mapping::new();
                        let outputs = transition
                            .outputs()
                            .iter()
                            .map(|output| serde_yaml::Value::String(output.to_string()))
                            .collect::<Vec<_>>();
                        transition_output.insert(
                            serde_yaml::Value::String("outputs".to_string()),
                            serde_yaml::Value::Sequence(outputs),
                        );
                        let finalize = match transition.finalize() {
                            None => vec![],
                            Some(finalize) => finalize
                                .iter()
                                .map(|input| serde_yaml::Value::String(input.to_string()))
                                .collect::<Vec<_>>(),
                        };
                        transition_output.insert(
                            serde_yaml::Value::String("finalize".to_string()),
                            serde_yaml::Value::Sequence(finalize),
                        );
                        execute.insert(
                            serde_yaml::Value::String(format!(
                                "{}/{}",
                                transition.program_id(),
                                transition.function_name()
                            )),
                            serde_yaml::Value::Mapping(transition_output),
                        );
                    }
                    output
                        .insert(serde_yaml::Value::String("execute".to_string()), serde_yaml::Value::Mapping(execute));
                    // Speculate on the transaction.
                    let transactions = match vm.speculate(construct_finalize_global_state(&vm), [transaction].iter()) {
                        Ok(transactions) => {
                            output.insert(
                                serde_yaml::Value::String("speculate".to_string()),
                                serde_yaml::Value::String(match transactions.iter().next().unwrap() {
                                    ConfirmedTransaction::AcceptedExecute(_, _, _) => {
                                        "the execution was accepted".to_string()
                                    }
                                    ConfirmedTransaction::RejectedExecute(_, _, _) => {
                                        "the execution was rejected".to_string()
                                    }
                                    ConfirmedTransaction::AcceptedDeploy(_, _, _)
                                    | ConfirmedTransaction::RejectedDeploy(_, _, _) => {
                                        unreachable!("unexpected deployment transaction")
                                    }
                                }),
                            );

                            transactions
                        }
                        Err(err) => {
                            output.insert(
                                serde_yaml::Value::String("speculate".to_string()),
                                serde_yaml::Value::String(err.to_string()),
                            );
                            return serde_yaml::Value::Mapping(output);
                        }
                    };
                    // Construct the next block.
                    let block = construct_next_block(&vm, &private_key, transactions, rng).unwrap();
                    // Add the next block.
                    output.insert(
                        serde_yaml::Value::String("add_next_block".to_string()),
                        serde_yaml::Value::String(match vm.add_next_block(&block) {
                            Ok(_) => "succeeded.".to_string(),
                            Err(err) => err.to_string(),
                        }),
                    );
                    serde_yaml::Value::Mapping(output)
                };

                run_test()
            })
            .collect::<Vec<_>>();
        // Check against the expected output.
        test.check(&outputs).unwrap();
        // Save the output.
        test.save(&outputs).unwrap();
    });
}

// A helper function to initialize the VM.
// Returns a VM and the first record in the genesis block.
#[allow(clippy::type_complexity)]
fn initialize_vm<R: Rng + CryptoRng>(
    private_key: &PrivateKey<CurrentNetwork>,
    rng: &mut R,
) -> (VM<CurrentNetwork, ConsensusMemory<CurrentNetwork>>, Vec<Record<CurrentNetwork, Plaintext<CurrentNetwork>>>) {
    // Initialize a VM.
    let vm: VM<CurrentNetwork, ConsensusMemory<CurrentNetwork>> =
        VM::from(ConsensusStore::open(None).unwrap()).unwrap();

    // Initialize the genesis block.
    let genesis = vm.genesis(private_key, rng).unwrap();

    // Select a record to spend.
    let view_key = ViewKey::try_from(private_key).unwrap();
    let records = genesis.transitions().cloned().flat_map(Transition::into_records).collect::<IndexMap<_, _>>();
    let records = records.values().map(|record| record.decrypt(&view_key).unwrap()).collect::<Vec<_>>();

    // Add the genesis block to the VM.
    vm.add_next_block(&genesis).unwrap();

    (vm, records)
}

// A helper function construct the desired number of fee records from an initial record, all owned by the same key.
fn construct_fee_records<C: ConsensusStorage<CurrentNetwork>, R: Rng + CryptoRng>(
    vm: &VM<CurrentNetwork, C>,
    private_key: &PrivateKey<CurrentNetwork>,
    records: Vec<Record<CurrentNetwork, Plaintext<CurrentNetwork>>>,
    num_fee_records: usize,
    rng: &mut R,
) -> Vec<(Record<CurrentNetwork, Plaintext<CurrentNetwork>>, u64)> {
    // Helper function to get the balance of a `credits.aleo` record.
    let get_balance = |record: &Record<CurrentNetwork, Plaintext<CurrentNetwork>>| -> u64 {
        match record.data().get(&Identifier::from_str("microcredits").unwrap()).unwrap() {
            Entry::Private(Plaintext::Literal(Literal::U64(amount), ..)) => **amount,
            _ => unreachable!("Invalid entry type for credits.aleo."),
        }
    };

    println!("Splitting the initial fee record into {} fee records.", num_fee_records);

    // Construct fee records for the tests.
    let mut fee_records = records
        .into_iter()
        .map(|record| {
            let balance = get_balance(&record);
            (record, balance)
        })
        .collect::<Vec<_>>();
    let mut fee_counter = 1;
    while fee_records.len() < num_fee_records {
        let mut transactions = Vec::with_capacity(fee_records.len());
        for (fee_record, balance) in fee_records.drain(..).collect_vec() {
            if fee_counter < num_fee_records {
                println!("Splitting out the {}-th record of size {}.", fee_counter, balance / 2);
                let (mut records, txns) = split(vm, private_key, fee_record, balance / 2, rng);
                let second = records.pop().unwrap();
                let first = records.pop().unwrap();
                let balance = get_balance(&first);
                fee_records.push((first, balance));
                let balance = get_balance(&second);
                fee_records.push((second, balance));
                transactions.extend(txns);
                fee_counter += 1;
            } else {
                fee_records.push((fee_record, balance));
            }
        }
        // Create a block for the fee transactions and add them to the VM.
        let transactions = vm.speculate(construct_finalize_global_state(vm), transactions.iter()).unwrap();
        let block = construct_next_block(vm, private_key, transactions, rng).unwrap();
        vm.add_next_block(&block).unwrap();
    }

    println!("Constructed fee records.");

    fee_records
}

// A helper function to construct the next block.
fn construct_next_block<C: ConsensusStorage<CurrentNetwork>, R: Rng + CryptoRng>(
    vm: &VM<CurrentNetwork, C>,
    private_key: &PrivateKey<CurrentNetwork>,
    transactions: Transactions<CurrentNetwork>,
    rng: &mut R,
) -> Result<Block<CurrentNetwork>> {
    // Get the most recent block.
    let block_hash =
        vm.block_store().get_block_hash(*vm.block_store().heights().max().unwrap().borrow()).unwrap().unwrap();
    let previous_block = vm.block_store().get_block(&block_hash).unwrap().unwrap();

    // Construct the metadata associated with the block.
    let metadata = Metadata::new(
        CurrentNetwork::ID,
        previous_block.round() + 1,
        previous_block.height() + 1,
        CurrentNetwork::STARTING_SUPPLY,
        0,
        0,
        CurrentNetwork::GENESIS_COINBASE_TARGET,
        CurrentNetwork::GENESIS_PROOF_TARGET,
        previous_block.last_coinbase_target(),
        previous_block.last_coinbase_timestamp(),
        CurrentNetwork::GENESIS_TIMESTAMP + 1,
    )?;
    // Construct the block header.
    let header = Header::from(
        *vm.block_store().current_state_root(),
        transactions.to_transactions_root().unwrap(),
        transactions.to_finalize_root().unwrap(),
        *<CurrentNetwork as Network>::merkle_tree_bhp::<{ RATIFICATIONS_DEPTH }>(&[]).unwrap().root(),
        Field::zero(),
        metadata,
    )?;

    // Construct the new block.
    Block::new_beacon(private_key, previous_block.hash(), header, transactions, vec![], None, rng)
}

// A helper function to invoke `credits.aleo/split`.
#[allow(clippy::type_complexity)]
fn split<C: ConsensusStorage<CurrentNetwork>, R: Rng + CryptoRng>(
    vm: &VM<CurrentNetwork, C>,
    private_key: &PrivateKey<CurrentNetwork>,
    record: Record<CurrentNetwork, Plaintext<CurrentNetwork>>,
    amount: u64,
    rng: &mut R,
) -> (Vec<Record<CurrentNetwork, Plaintext<CurrentNetwork>>>, Vec<Transaction<CurrentNetwork>>) {
    let inputs = vec![Value::Record(record), Value::Plaintext(Plaintext::from(Literal::U64(U64::new(amount))))];
    let transaction = vm.execute(private_key, ("credits.aleo", "split"), inputs.iter(), None, None, rng).unwrap();
    let records = transaction
        .records()
        .map(|(_, record)| record.decrypt(&ViewKey::try_from(private_key).unwrap()).unwrap())
        .collect_vec();
    assert_eq!(records.len(), 2);
    (records, vec![transaction])
}

// Construct `FinalizeGlobalState` from the current `VM` state.
fn construct_finalize_global_state<C: ConsensusStorage<CurrentNetwork>>(
    vm: &VM<CurrentNetwork, C>,
) -> FinalizeGlobalState {
    // Retrieve the latest block.
    let block_height = *vm.block_store().heights().max().unwrap().clone();
    let latest_block_hash = vm.block_store().get_block_hash(block_height).unwrap().unwrap();
    let latest_block = vm.block_store().get_block(&latest_block_hash).unwrap().unwrap();
    // Retrieve the latest round.
    let latest_round = latest_block.round();
    // Retrieve the latest height.
    let latest_height = latest_block.height();
    // Retrieve the latest cumulative weight.
    let latest_cumulative_weight = latest_block.cumulative_weight();

    // Compute the next round number./
    let next_round = latest_round.saturating_add(1);
    // Compute the next height.
    let next_height = latest_height.saturating_add(1);

    // Construct the finalize state.
    FinalizeGlobalState::new::<CurrentNetwork>(
        next_round,
        next_height,
        latest_cumulative_weight,
        0u128,
        latest_block.hash(),
    )
    .unwrap()
}
