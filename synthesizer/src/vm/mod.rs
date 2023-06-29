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

mod helpers;

mod authorize;
mod deploy;
mod execute;
mod execute_fee;
mod finalize;
mod verify;

pub use finalize::FinalizeMode;

use crate::{
    atomic_finalize,
    block::{Block, ConfirmedTransaction, Deployment, Execution, Fee, Header, Transaction, Transactions},
    cast_mut_ref,
    cast_ref,
    process,
    process::{Authorization, FinalizeGlobalState, Process, Program, Trace},
    query::Query,
    stack::FinalizeStoreTrait,
    store::{BlockStore, ConsensusStorage, ConsensusStore, FinalizeStore, TransactionStore, TransitionStore},
    TransactionStorage,
};
use console::{
    account::{Address, PrivateKey},
    network::prelude::*,
    program::{Entry, Identifier, Literal, Locator, Plaintext, ProgramID, ProgramOwner, Record, Response, Value},
    types::Field,
};

use aleo_std::prelude::{finish, lap, timer};
use parking_lot::RwLock;
use std::sync::Arc;

#[derive(Clone)]
pub struct VM<N: Network, C: ConsensusStorage<N>> {
    /// The process.
    process: Arc<RwLock<Process<N>>>,
    /// The VM store.
    store: ConsensusStore<N, C>,
}

impl<N: Network, C: ConsensusStorage<N>> VM<N, C> {
    /// Initializes the VM from storage.
    #[inline]
    pub fn from(store: ConsensusStore<N, C>) -> Result<Self> {
        // Initialize a new process.
        let mut process = Process::load()?;

        // Initialize the store for 'credits.aleo'.
        let credits = Program::<N>::credits()?;
        for mapping in credits.mappings().values() {
            // Ensure that all mappings are initialized.
            if !store.finalize_store().contains_mapping_confirmed(credits.id(), mapping.name())? {
                // Initialize the mappings for 'credits.aleo'.
                store.finalize_store().initialize_mapping(credits.id(), mapping.name())?;
            }
        }

        // A helper function to load the program into the process, and recursively load all imports.
        fn load_deployment_and_imports<N: Network, T: TransactionStorage<N>>(
            process: &mut Process<N>,
            transaction_store: &TransactionStore<N, T>,
            transaction_id: N::TransactionID,
        ) -> Result<()> {
            // Retrieve the deployment from the transaction id.
            let deployment = match transaction_store.get_deployment(&transaction_id)? {
                Some(deployment) => deployment,
                None => bail!("Deployment transaction '{transaction_id}' is not found in storage."),
            };

            // Fetch the program from the deployment.
            let program = deployment.program();
            let program_id = program.id();

            // Return early if the program is already loaded.
            if process.contains_program(program_id) {
                return Ok(());
            }

            // Iterate through the program imports.
            for import_program_id in program.imports().keys() {
                // Add the imports to the process if does not exist yet.
                if !process.contains_program(import_program_id) {
                    // Fetch the deployment transaction id.
                    let Some(transaction_id) = transaction_store
                        .deployment_store()
                        .find_transaction_id_from_program_id(import_program_id)?
                    else {
                        bail!("Transaction id for '{program_id}' is not found in storage.");
                    };

                    // Recursively load the deployment and its imports.
                    load_deployment_and_imports(process, transaction_store, transaction_id)?
                }
            }

            // Load the deployment if it does not exist in the process yet.
            if !process.contains_program(program_id) {
                process.load_deployment(&deployment)?;
            }

            Ok(())
        }

        // Retrieve the transaction store.
        let transaction_store = store.transaction_store();
        // Load the deployments from the store.
        for transaction_id in transaction_store.deployment_transaction_ids() {
            // Load the deployment and its imports.
            load_deployment_and_imports(&mut process, transaction_store, *transaction_id)?;
        }

        // Return the new VM.
        Ok(Self { process: Arc::new(RwLock::new(process)), store })
    }

    /// Returns `true` if a program with the given program ID exists.
    #[inline]
    pub fn contains_program(&self, program_id: &ProgramID<N>) -> bool {
        self.process.read().contains_program(program_id)
    }

    /// Returns the process.
    #[inline]
    pub fn process(&self) -> Arc<RwLock<Process<N>>> {
        self.process.clone()
    }
}

impl<N: Network, C: ConsensusStorage<N>> VM<N, C> {
    /// Returns the finalize store.
    #[inline]
    pub fn finalize_store(&self) -> &FinalizeStore<N, C::FinalizeStorage> {
        self.store.finalize_store()
    }

    /// Returns the block store.
    #[inline]
    pub fn block_store(&self) -> &BlockStore<N, C::BlockStorage> {
        self.store.block_store()
    }

    /// Returns the transaction store.
    #[inline]
    pub fn transaction_store(&self) -> &TransactionStore<N, C::TransactionStorage> {
        self.store.transaction_store()
    }

    /// Returns the transition store.
    #[inline]
    pub fn transition_store(&self) -> &TransitionStore<N, C::TransitionStorage> {
        self.store.transition_store()
    }
}

impl<N: Network, C: ConsensusStorage<N>> VM<N, C> {
    /// Returns a new genesis block.
    pub fn genesis<R: Rng + CryptoRng>(&self, private_key: &PrivateKey<N>, rng: &mut R) -> Result<Block<N>> {
        // Prepare the caller.
        let caller = Address::try_from(private_key)?;
        // Prepare the locator.
        let locator = ("credits.aleo", "mint");
        // Prepare the amount for each call to the mint function.
        let amount = N::STARTING_SUPPLY.saturating_div(Block::<N>::NUM_GENESIS_TRANSACTIONS as u64);
        // Prepare the function inputs.
        let inputs = [caller.to_string(), format!("{amount}_u64")];

        // Prepare the mint transactions.
        let transactions = (0u32..u32::try_from(Block::<N>::NUM_GENESIS_TRANSACTIONS)?)
            .map(|index| {
                // Execute the mint function.
                let transaction = self.execute(private_key, locator, inputs.iter(), None, None, rng)?;
                // Prepare the confirmed transaction.
                ConfirmedTransaction::accepted_execute(index, transaction, vec![])
            })
            .collect::<Result<Transactions<_>>>()?;

        // Prepare the block header.
        let header = Header::genesis(&transactions)?;
        // Prepare the previous block hash.
        let previous_hash = N::BlockHash::default();

        // Prepare the coinbase solution.
        let coinbase_solution = None; // The genesis block does not require a coinbase solution.

        // Construct the block.
        let block = Block::new(private_key, previous_hash, header, transactions, vec![], coinbase_solution, rng)?;
        // Ensure the block is valid genesis block.
        match block.is_genesis() {
            true => Ok(block),
            false => bail!("Failed to initialize a genesis block"),
        }
    }

    /// Adds the given block into the VM.
    #[inline]
    pub fn add_next_block(&self, block: &Block<N>) -> Result<()> {
        // Construct the finalize state.
        let state = FinalizeGlobalState::new::<N>(
            block.round(),
            block.height(),
            block.cumulative_weight(),
            block.cumulative_proof_target(),
            block.previous_hash(),
        )?;

        // First, insert the block.
        self.block_store().insert(block)?;
        // Next, finalize the transactions.
        match self.finalize(state, block.transactions()) {
            Ok(_) => {
                // TODO (howardwu): Check the accepted, rejected, and finalize operations match the block.
                Ok(())
            }
            Err(error) => {
                // Rollback the block.
                self.block_store().remove_last_n(1)?;
                // Return the error.
                Err(error)
            }
        }
    }
}

#[cfg(test)]
pub(crate) mod test_helpers {
    use super::*;
    use crate::{
        block::{Block, Fee, Header, Metadata, Transition},
        process::Program,
        store::helpers::memory::ConsensusMemory,
    };
    use console::{
        account::{Address, ViewKey},
        network::Testnet3,
        program::{Value, RATIFICATIONS_DEPTH},
        types::Field,
    };

    use indexmap::IndexMap;
    use once_cell::sync::OnceCell;
    use std::borrow::Borrow;

    pub(crate) type CurrentNetwork = Testnet3;

    /// Samples a new finalize state.
    pub(crate) fn sample_finalize_state(block_height: u32) -> FinalizeGlobalState {
        FinalizeGlobalState::from(block_height, [0u8; 32])
    }

    pub(crate) fn sample_ratifications_root() -> Field<CurrentNetwork> {
        *<CurrentNetwork as Network>::merkle_tree_bhp::<RATIFICATIONS_DEPTH>(&[]).unwrap().root()
    }

    pub(crate) fn sample_vm() -> VM<CurrentNetwork, ConsensusMemory<CurrentNetwork>> {
        // Initialize a new VM.
        VM::from(ConsensusStore::open(None).unwrap()).unwrap()
    }

    pub(crate) fn sample_genesis_private_key(rng: &mut TestRng) -> PrivateKey<CurrentNetwork> {
        static INSTANCE: OnceCell<PrivateKey<CurrentNetwork>> = OnceCell::new();
        *INSTANCE.get_or_init(|| {
            // Initialize a new caller.
            PrivateKey::<CurrentNetwork>::new(rng).unwrap()
        })
    }

    pub(crate) fn sample_genesis_block(rng: &mut TestRng) -> Block<CurrentNetwork> {
        static INSTANCE: OnceCell<Block<CurrentNetwork>> = OnceCell::new();
        INSTANCE
            .get_or_init(|| {
                // Initialize the VM.
                let vm = crate::vm::test_helpers::sample_vm();
                // Initialize a new caller.
                let caller_private_key = crate::vm::test_helpers::sample_genesis_private_key(rng);
                // Return the block.
                vm.genesis(&caller_private_key, rng).unwrap()
            })
            .clone()
    }

    pub(crate) fn sample_vm_with_genesis_block(
        rng: &mut TestRng,
    ) -> VM<CurrentNetwork, ConsensusMemory<CurrentNetwork>> {
        // Initialize the VM.
        let vm = crate::vm::test_helpers::sample_vm();
        // Initialize the genesis block.
        let genesis = crate::vm::test_helpers::sample_genesis_block(rng);
        // Update the VM.
        vm.add_next_block(&genesis).unwrap();
        // Return the VM.
        vm
    }

    pub(crate) fn sample_program() -> Program<CurrentNetwork> {
        static INSTANCE: OnceCell<Program<CurrentNetwork>> = OnceCell::new();
        INSTANCE
            .get_or_init(|| {
                // Initialize a new program.
                Program::<CurrentNetwork>::from_str(
                    r"
program testing.aleo;

struct message:
    amount as u128;

mapping account:
    key owner as address.public;
    value amount as u64.public;

record token:
    owner as address.private;
    amount as u64.private;

function mint:
    input r0 as address.private;
    input r1 as u64.private;
    cast r0 r1 into r2 as token.record;
    output r2 as token.record;

function compute:
    input r0 as message.private;
    input r1 as message.public;
    input r2 as message.private;
    input r3 as token.record;
    add r0.amount r1.amount into r4;
    cast r3.owner r3.amount into r5 as token.record;
    output r4 as u128.public;
    output r5 as token.record;",
                )
                .unwrap()
            })
            .clone()
    }

    pub(crate) fn sample_deployment_transaction(rng: &mut TestRng) -> Transaction<CurrentNetwork> {
        static INSTANCE: OnceCell<Transaction<CurrentNetwork>> = OnceCell::new();
        INSTANCE
            .get_or_init(|| {
                // Initialize the program.
                let program = sample_program();

                // Initialize a new caller.
                let caller_private_key = crate::vm::test_helpers::sample_genesis_private_key(rng);
                let caller_view_key = ViewKey::try_from(&caller_private_key).unwrap();

                // Initialize the genesis block.
                let genesis = crate::vm::test_helpers::sample_genesis_block(rng);

                // Fetch the unspent records.
                let records =
                    genesis.transitions().cloned().flat_map(Transition::into_records).collect::<IndexMap<_, _>>();
                trace!("Unspent Records:\n{:#?}", records);

                // Prepare the fee.
                let credits = records.values().next().unwrap().decrypt(&caller_view_key).unwrap();
                let fee = (credits, 10);

                // Initialize the VM.
                let vm = sample_vm();
                // Update the VM.
                vm.add_next_block(&genesis).unwrap();

                // Deploy.
                let transaction = vm.deploy(&caller_private_key, &program, fee, None, rng).unwrap();
                // Verify.
                assert!(vm.verify_transaction(&transaction, None));
                // Return the transaction.
                transaction
            })
            .clone()
    }

    pub(crate) fn sample_execution_transaction_without_fee(rng: &mut TestRng) -> Transaction<CurrentNetwork> {
        static INSTANCE: OnceCell<Transaction<CurrentNetwork>> = OnceCell::new();
        INSTANCE
            .get_or_init(|| {
                // Initialize a new caller.
                let caller_private_key = crate::vm::test_helpers::sample_genesis_private_key(rng);
                let caller_view_key = ViewKey::try_from(&caller_private_key).unwrap();
                let address = Address::try_from(&caller_private_key).unwrap();

                // Initialize the genesis block.
                let genesis = crate::vm::test_helpers::sample_genesis_block(rng);

                // Fetch the unspent records.
                let records =
                    genesis.transitions().cloned().flat_map(Transition::into_records).collect::<IndexMap<_, _>>();
                trace!("Unspent Records:\n{:#?}", records);

                // Select a record to spend.
                let record = records.values().next().unwrap().decrypt(&caller_view_key).unwrap();

                // Initialize the VM.
                let vm = sample_vm();
                // Update the VM.
                vm.add_next_block(&genesis).unwrap();

                // Prepare the inputs.
                let inputs = [
                    Value::<CurrentNetwork>::Record(record),
                    Value::<CurrentNetwork>::from_str(&address.to_string()).unwrap(),
                    Value::<CurrentNetwork>::from_str("1u64").unwrap(),
                ]
                .into_iter();

                // Authorize.
                let authorization =
                    vm.authorize(&caller_private_key, "credits.aleo", "transfer_private", inputs, rng).unwrap();
                assert_eq!(authorization.len(), 1);

                // Execute.
                let transaction = vm.execute_authorization(authorization, None, None, rng).unwrap();
                // Verify.
                assert!(!vm.verify_transaction(&transaction, None));
                // Return the transaction.
                transaction
            })
            .clone()
    }

    pub(crate) fn sample_execution_transaction_with_fee(rng: &mut TestRng) -> Transaction<CurrentNetwork> {
        static INSTANCE: OnceCell<Transaction<CurrentNetwork>> = OnceCell::new();
        INSTANCE
            .get_or_init(|| {
                // Initialize a new caller.
                let caller_private_key = crate::vm::test_helpers::sample_genesis_private_key(rng);
                let caller_view_key = ViewKey::try_from(&caller_private_key).unwrap();
                let address = Address::try_from(&caller_private_key).unwrap();

                // Initialize the genesis block.
                let genesis = crate::vm::test_helpers::sample_genesis_block(rng);

                // Fetch the unspent records.
                let records =
                    genesis.transitions().cloned().flat_map(Transition::into_records).collect::<IndexMap<_, _>>();
                trace!("Unspent Records:\n{:#?}", records);

                // Select a record to spend.
                let record = records.values().next().unwrap().decrypt(&caller_view_key).unwrap();

                // Initialize the VM.
                let vm = sample_vm();
                // Update the VM.
                vm.add_next_block(&genesis).unwrap();

                // Prepare the inputs.
                let inputs = [
                    Value::<CurrentNetwork>::from_str(&address.to_string()).unwrap(),
                    Value::<CurrentNetwork>::from_str("1u64").unwrap(),
                ]
                .into_iter();

                // Prepare the fee.
                let fee = Some((record, 100));

                // Execute.
                let transaction =
                    vm.execute(&caller_private_key, ("credits.aleo", "mint"), inputs, fee, None, rng).unwrap();
                // Verify.
                assert!(vm.verify_transaction(&transaction, None));
                // Return the transaction.
                transaction
            })
            .clone()
    }

    pub(crate) fn sample_fee(rng: &mut TestRng) -> Fee<CurrentNetwork> {
        static INSTANCE: OnceCell<Fee<CurrentNetwork>> = OnceCell::new();
        INSTANCE
            .get_or_init(|| {
                // Initialize a new caller.
                let caller_private_key = crate::vm::test_helpers::sample_genesis_private_key(rng);
                let caller_view_key = ViewKey::try_from(&caller_private_key).unwrap();

                // Initialize the genesis block.
                let genesis = crate::vm::test_helpers::sample_genesis_block(rng);

                // Fetch the unspent records.
                let records =
                    genesis.transitions().cloned().flat_map(Transition::into_records).collect::<IndexMap<_, _>>();
                trace!("Unspent Records:\n{:#?}", records);

                // Select a record to spend.
                let record = records.values().next().unwrap().decrypt(&caller_view_key).unwrap();

                // Initialize the VM.
                let vm = sample_vm();
                // Update the VM.
                vm.add_next_block(&genesis).unwrap();

                // Sample a random rejected ID.
                let rejected_id = Field::rand(rng);

                // Execute.
                let (_response, fee) =
                    vm.execute_fee_raw(&caller_private_key, record, 1u64, rejected_id, None, rng).unwrap();
                // Verify.
                assert!(vm.verify_fee(&fee, rejected_id));
                // Return the fee.
                fee
            })
            .clone()
    }

    pub(crate) fn sample_fee_transaction(rng: &mut TestRng) -> Transaction<CurrentNetwork> {
        static INSTANCE: OnceCell<Transaction<CurrentNetwork>> = OnceCell::new();
        INSTANCE
            .get_or_init(|| {
                // Initialize a fee.
                let fee = crate::vm::test_helpers::sample_fee(rng);
                // Return the fee transaction.
                Transaction::from_fee(fee).unwrap()
            })
            .clone()
    }

    pub fn sample_next_block<R: Rng + CryptoRng>(
        vm: &VM<Testnet3, ConsensusMemory<Testnet3>>,
        private_key: &PrivateKey<Testnet3>,
        transactions: &[Transaction<Testnet3>],
        rng: &mut R,
    ) -> Result<Block<Testnet3>> {
        // Get the most recent block.
        let block_hash =
            vm.block_store().get_block_hash(*vm.block_store().heights().max().unwrap().borrow()).unwrap().unwrap();
        let previous_block = vm.block_store().get_block(&block_hash).unwrap().unwrap();

        // Construct the new block header.
        let transactions = vm.speculate(sample_finalize_state(1), transactions.iter())?;
        // Construct the metadata associated with the block.
        let metadata = Metadata::new(
            Testnet3::ID,
            previous_block.round() + 1,
            previous_block.height() + 1,
            Testnet3::STARTING_SUPPLY,
            0,
            0,
            Testnet3::GENESIS_COINBASE_TARGET,
            Testnet3::GENESIS_PROOF_TARGET,
            previous_block.last_coinbase_target(),
            previous_block.last_coinbase_timestamp(),
            Testnet3::GENESIS_TIMESTAMP + 1,
        )?;

        let header = Header::from(
            *vm.block_store().current_state_root(),
            transactions.to_transactions_root().unwrap(),
            transactions.to_finalize_root().unwrap(),
            crate::vm::test_helpers::sample_ratifications_root(),
            Field::zero(),
            metadata,
        )?;

        // Construct the new block.
        Block::new(private_key, previous_block.hash(), header, transactions, vec![], None, rng)
    }

    #[test]
    fn test_multiple_deployments_and_multiple_executions() {
        let rng = &mut TestRng::default();

        // Initialize a new caller.
        let caller_private_key = crate::vm::test_helpers::sample_genesis_private_key(rng);
        let caller_view_key = ViewKey::try_from(&caller_private_key).unwrap();

        // Initialize the genesis block.
        let genesis = crate::vm::test_helpers::sample_genesis_block(rng);

        // Fetch the unspent records.
        let records = genesis.transitions().cloned().flat_map(Transition::into_records).collect::<IndexMap<_, _>>();
        trace!("Unspent Records:\n{:#?}", records);

        // Select a record to spend.
        let record = records.values().next().unwrap().decrypt(&caller_view_key).unwrap();

        // Initialize the VM.
        let vm = sample_vm();
        // Update the VM.
        vm.add_next_block(&genesis).unwrap();

        // Split once.
        let transaction = vm
            .execute(
                &caller_private_key,
                ("credits.aleo", "split"),
                [Value::Record(record), Value::from_str("1000000000u64").unwrap()].iter(), // 1000 credits
                None,
                None,
                rng,
            )
            .unwrap();
        let records = transaction.records().collect_vec();
        let first_record = records[0].1.clone().decrypt(&caller_view_key).unwrap();
        let second_record = records[1].1.clone().decrypt(&caller_view_key).unwrap();
        let block = sample_next_block(&vm, &caller_private_key, &[transaction], rng).unwrap();
        vm.add_next_block(&block).unwrap();

        // Split again.
        let mut transactions = Vec::new();
        let transaction = vm
            .execute(
                &caller_private_key,
                ("credits.aleo", "split"),
                [Value::Record(first_record), Value::from_str("100000000u64").unwrap()].iter(), // 100 credits
                None,
                None,
                rng,
            )
            .unwrap();
        let records = transaction.records().collect_vec();
        let first_record = records[0].1.clone().decrypt(&caller_view_key).unwrap();
        let third_record = records[1].1.clone().decrypt(&caller_view_key).unwrap();
        transactions.push(transaction);
        // Split again.
        let transaction = vm
            .execute(
                &caller_private_key,
                ("credits.aleo", "split"),
                [Value::Record(second_record), Value::from_str("100000000u64").unwrap()].iter(), // 100 credits
                None,
                None,
                rng,
            )
            .unwrap();
        let records = transaction.records().collect_vec();
        let second_record = records[0].1.clone().decrypt(&caller_view_key).unwrap();
        let fourth_record = records[1].1.clone().decrypt(&caller_view_key).unwrap();
        transactions.push(transaction);
        // Add the split transactions to a block and update the VM.
        let fee_block = sample_next_block(&vm, &caller_private_key, &transactions, rng).unwrap();
        vm.add_next_block(&fee_block).unwrap();

        // Deploy the programs.
        let first_program = r"
program test_program_1.aleo;
mapping map_0:
    key left as field.public;
    value right as field.public;
function init:
    finalize;
finalize init:
    set 0field into map_0[0field];
function getter:
    finalize;
finalize getter:
    get map_0[0field] into r0;
        ";
        let second_program = r"
program test_program_2.aleo;
mapping map_0:
    key left as field.public;
    value right as field.public;
function init:
    finalize;
finalize init:
    set 0field into map_0[0field];
function getter:
    finalize;
finalize getter:
    get map_0[0field] into r0;
        ";
        let first_deployment = vm
            .deploy(&caller_private_key, &Program::from_str(first_program).unwrap(), (first_record, 1), None, rng)
            .unwrap();
        let second_deployment = vm
            .deploy(&caller_private_key, &Program::from_str(second_program).unwrap(), (second_record, 1), None, rng)
            .unwrap();
        let deployment_block =
            sample_next_block(&vm, &caller_private_key, &[first_deployment, second_deployment], rng).unwrap();
        vm.add_next_block(&deployment_block).unwrap();

        // Execute the programs.
        let first_execution = vm
            .execute(
                &caller_private_key,
                ("test_program_1.aleo", "init"),
                Vec::<Value<Testnet3>>::new().iter(),
                Some((third_record, 1)),
                None,
                rng,
            )
            .unwrap();
        let second_execution = vm
            .execute(
                &caller_private_key,
                ("test_program_2.aleo", "init"),
                Vec::<Value<Testnet3>>::new().iter(),
                Some((fourth_record, 1)),
                None,
                rng,
            )
            .unwrap();
        let execution_block =
            sample_next_block(&vm, &caller_private_key, &[first_execution, second_execution], rng).unwrap();
        vm.add_next_block(&execution_block).unwrap();
    }

    #[test]
    fn test_load_deployments_with_imports() {
        // NOTE: This seed was chosen for the CI's RNG to ensure that the test passes.
        let rng = &mut TestRng::fixed(123456789);

        // Initialize a new caller.
        let caller_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let caller_view_key = ViewKey::try_from(&caller_private_key).unwrap();

        // Initialize the VM.
        let vm = crate::vm::test_helpers::sample_vm();
        // Initialize the genesis block.
        let genesis = vm.genesis(&caller_private_key, rng).unwrap();
        // Update the VM.
        vm.add_next_block(&genesis).unwrap();

        // Fetch the unspent records.
        let records = genesis.transitions().cloned().flat_map(Transition::into_records).collect::<Vec<(_, _)>>();
        trace!("Unspent Records:\n{:#?}", records);
        let record_0 = records[0].1.decrypt(&caller_view_key).unwrap();
        let record_1 = records[1].1.decrypt(&caller_view_key).unwrap();
        let record_2 = records[2].1.decrypt(&caller_view_key).unwrap();
        let record_3 = records[3].1.decrypt(&caller_view_key).unwrap();

        // Create the deployment for the first program.
        let program_1 = r"
program first_program.aleo;

function c:
    input r0 as u8.private;
    input r1 as u8.private;
    add r0 r1 into r2;
    output r2 as u8.private;
        ";
        let deployment_1 =
            vm.deploy(&caller_private_key, &Program::from_str(program_1).unwrap(), (record_0, 0), None, rng).unwrap();

        // Deploy the first program.
        let deployment_block = sample_next_block(&vm, &caller_private_key, &[deployment_1.clone()], rng).unwrap();
        vm.add_next_block(&deployment_block).unwrap();

        // Create the deployment for the second program.
        let program_2 = r"
import first_program.aleo;

program second_program.aleo;

function b:
    input r0 as u8.private;
    input r1 as u8.private;
    call first_program.aleo/c r0 r1 into r2;
    output r2 as u8.private;
        ";
        let deployment_2 =
            vm.deploy(&caller_private_key, &Program::from_str(program_2).unwrap(), (record_1, 0), None, rng).unwrap();

        // Deploy the second program.
        let deployment_block = sample_next_block(&vm, &caller_private_key, &[deployment_2.clone()], rng).unwrap();
        vm.add_next_block(&deployment_block).unwrap();

        // Create the deployment for the third program.
        let program_3 = r"
import second_program.aleo;

program third_program.aleo;

function a:
    input r0 as u8.private;
    input r1 as u8.private;
    call second_program.aleo/b r0 r1 into r2;
    output r2 as u8.private;
        ";
        let deployment_3 =
            vm.deploy(&caller_private_key, &Program::from_str(program_3).unwrap(), (record_2, 0), None, rng).unwrap();

        // Create the deployment for the fourth program.
        let program_4 = r"
import second_program.aleo;
import first_program.aleo;

program fourth_program.aleo;

function a:
    input r0 as u8.private;
    input r1 as u8.private;
    call second_program.aleo/b r0 r1 into r2;
    output r2 as u8.private;
        ";
        let deployment_4 =
            vm.deploy(&caller_private_key, &Program::from_str(program_4).unwrap(), (record_3, 0), None, rng).unwrap();

        // Deploy the third and fourth program together.
        let deployment_block =
            sample_next_block(&vm, &caller_private_key, &[deployment_3.clone(), deployment_4.clone()], rng).unwrap();
        vm.add_next_block(&deployment_block).unwrap();

        // Check that the iterator ordering is not the same as the deployment ordering.
        let deployment_transaction_ids =
            vm.transaction_store().deployment_transaction_ids().map(|id| *id).collect::<Vec<_>>();
        // This `assert_ne` check is here to ensure that we are properly loading imports even though any order will work for `VM::from`.
        // Note: `deployment_transaction_ids` is sorted lexicographically by transaction id, so the order may change if we update internal methods.
        assert_ne!(deployment_transaction_ids, vec![
            deployment_1.id(),
            deployment_2.id(),
            deployment_3.id(),
            deployment_4.id()
        ]);

        // Enforce that the VM can load properly with the imports.
        assert!(VM::from(vm.store.clone()).is_ok());
    }

    #[test]
    fn test_multiple_external_calls() {
        let rng = &mut TestRng::default();

        // Initialize a new caller.
        let caller_private_key = crate::vm::test_helpers::sample_genesis_private_key(rng);
        let caller_view_key = ViewKey::try_from(&caller_private_key).unwrap();
        let address = Address::try_from(&caller_private_key).unwrap();

        // Initialize the genesis block.
        let genesis = crate::vm::test_helpers::sample_genesis_block(rng);

        // Fetch the unspent records.
        let records =
            genesis.transitions().cloned().flat_map(Transition::into_records).take(3).collect::<IndexMap<_, _>>();
        trace!("Unspent Records:\n{:#?}", records);
        let record_0 = records.values().next().unwrap().decrypt(&caller_view_key).unwrap();
        let record_1 = records.values().nth(1).unwrap().decrypt(&caller_view_key).unwrap();
        let record_2 = records.values().nth(2).unwrap().decrypt(&caller_view_key).unwrap();

        // Initialize the VM.
        let vm = sample_vm();
        // Update the VM.
        vm.add_next_block(&genesis).unwrap();

        // Deploy the program.
        let program = Program::from_str(
            r"
import credits.aleo;

program test_multiple_external_calls.aleo;

function multitransfer:
    input r0 as credits.aleo/credits.record;
    input r1 as address.private;
    input r2 as u64.private;
    call credits.aleo/transfer_private r0 r1 r2 into r3 r4;
    call credits.aleo/transfer_private r4 r1 r2 into r5 r6;
    output r4 as credits.aleo/credits.record;
    output r5 as credits.aleo/credits.record;
    output r6 as credits.aleo/credits.record;
    ",
        )
        .unwrap();
        let deployment = vm.deploy(&caller_private_key, &program, (record_0, 1), None, rng).unwrap();
        vm.add_next_block(&sample_next_block(&vm, &caller_private_key, &[deployment], rng).unwrap()).unwrap();

        // Execute the programs.
        let inputs = [
            Value::<Testnet3>::Record(record_1),
            Value::<Testnet3>::from_str(&address.to_string()).unwrap(),
            Value::<Testnet3>::from_str("10u64").unwrap(),
        ];
        let execution = vm
            .execute(
                &caller_private_key,
                ("test_multiple_external_calls.aleo", "multitransfer"),
                inputs.into_iter(),
                Some((record_2, 1)),
                None,
                rng,
            )
            .unwrap();
        vm.add_next_block(&sample_next_block(&vm, &caller_private_key, &[execution], rng).unwrap()).unwrap();
    }
}
