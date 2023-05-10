// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// The snarkVM library is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// The snarkVM library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with the snarkVM library. If not, see <https://www.gnu.org/licenses/>.

mod helpers;

mod authorize;
mod deploy;
mod execute;
mod finalize;
mod verify;

pub use finalize::FinalizeMode;

use crate::{
    atomic_finalize,
    block::{Block, Transaction, Transition},
    cast_ref,
    process,
    process::{Authorization, Deployment, Execution, Fee, Inclusion, InclusionAssignment, Process, Query},
    program::Program,
    store::{BlockStore, ConsensusStorage, ConsensusStore, FinalizeStore, TransactionStore, TransitionStore},
    CallMetrics,
};
use console::{
    account::PrivateKey,
    network::prelude::*,
    program::{Entry, Identifier, Literal, Plaintext, ProgramID, Record, Response, Value},
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

        // Retrieve the transaction store.
        let transaction_store = store.transaction_store();
        // Load the deployments from the store.
        for transaction_id in transaction_store.deployment_transaction_ids() {
            // Retrieve the deployment.
            match transaction_store.get_deployment(&transaction_id)? {
                // Load the deployment.
                Some(deployment) => process.load_deployment(&deployment)?,
                None => bail!("Deployment transaction '{transaction_id}' is not found in storage."),
            };
        }

        // Return the new VM.
        Ok(Self { process: Arc::new(RwLock::new(process)), store })
    }

    /// Returns `true` if a program with the given program ID exists.
    #[inline]
    pub fn contains_program(&self, program_id: &ProgramID<N>) -> bool {
        self.process.read().contains_program(program_id)
    }

    /// Adds the given block into the VM.
    #[inline]
    pub fn add_next_block(&self, block: &Block<N>) -> Result<()> {
        // First, insert the block.
        self.block_store().insert(block)?;
        // Next, finalize the transactions.
        match self.finalize(block.transactions()) {
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

#[cfg(test)]
pub(crate) mod test_helpers {
    use super::*;
    use crate::{
        program::Program,
        store::helpers::memory::ConsensusMemory,
        Block,
        Fee,
        Header,
        Inclusion,
        Metadata,
        Transition,
    };
    use console::{
        account::{Address, ViewKey},
        network::Testnet3,
        program::Value,
    };

    use indexmap::IndexMap;
    use once_cell::sync::OnceCell;
    use std::borrow::Borrow;

    pub(crate) type CurrentNetwork = Testnet3;

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
                Block::genesis(&vm, &caller_private_key, rng).unwrap()
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
                let transaction = Transaction::deploy(&vm, &caller_private_key, &program, fee, None, rng).unwrap();
                // Verify.
                assert!(vm.verify_transaction(&transaction));
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
                let authorization = vm.authorize(&caller_private_key, "credits.aleo", "transfer", inputs, rng).unwrap();
                assert_eq!(authorization.len(), 1);

                // Execute.
                let transaction = Transaction::execute_authorization(&vm, authorization, None, None, rng).unwrap();
                // Verify.
                assert!(!vm.verify_transaction(&transaction));
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

                // Authorize.
                let authorization = vm.authorize(&caller_private_key, "credits.aleo", "mint", inputs, rng).unwrap();
                assert_eq!(authorization.len(), 1);

                // Execute the fee.
                let fee = Transaction::execute_fee(&vm, &caller_private_key, record, 100, None, rng).unwrap();

                // Execute.
                let transaction = Transaction::execute_authorization(&vm, authorization, Some(fee), None, rng).unwrap();
                // Verify.
                assert!(vm.verify_transaction(&transaction));
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

                // Execute.
                let (_response, fee, _metrics) = vm.execute_fee(&caller_private_key, record, 1u64, None, rng).unwrap();
                // Verify.
                assert!(vm.verify_fee(&fee));
                assert!(Inclusion::verify_fee(&fee).is_ok());
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
        let transactions = vm.speculate(transactions.iter())?;
        // Construct the metadata associated with the block.
        let metadata = Metadata::new(
            Testnet3::ID,
            previous_block.round() + 1,
            previous_block.height() + 1,
            Testnet3::STARTING_SUPPLY,
            0,
            Testnet3::GENESIS_COINBASE_TARGET,
            Testnet3::GENESIS_PROOF_TARGET,
            previous_block.last_coinbase_target(),
            previous_block.last_coinbase_timestamp(),
            Testnet3::GENESIS_TIMESTAMP + 1,
        )?;

        let header = Header::from(
            *vm.block_store().current_state_root(),
            transactions.to_root().unwrap(),
            Field::zero(),
            // TODO (howardwu): Revisit this.
            // vm.finalize_store().current_finalize_root(),
            Field::zero(),
            metadata,
        )?;

        // Construct the new block.
        Block::new(private_key, previous_block.hash(), header, transactions, None, rng)
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
        let transaction = Transaction::execute(
            &vm,
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
        let transaction = Transaction::execute(
            &vm,
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
        let transaction = Transaction::execute(
            &vm,
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
program test_1.aleo;
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
program test_2.aleo;
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
        let first_deployment = Transaction::deploy(
            &vm,
            &caller_private_key,
            &Program::from_str(first_program).unwrap(),
            (first_record, 1),
            None,
            rng,
        )
        .unwrap();
        let second_deployment = Transaction::deploy(
            &vm,
            &caller_private_key,
            &Program::from_str(second_program).unwrap(),
            (second_record, 1),
            None,
            rng,
        )
        .unwrap();
        let deployment_block =
            sample_next_block(&vm, &caller_private_key, &[first_deployment, second_deployment], rng).unwrap();
        vm.add_next_block(&deployment_block).unwrap();

        // Execute the programs.
        let first_execution = Transaction::execute(
            &vm,
            &caller_private_key,
            ("test_1.aleo", "init"),
            Vec::<Value<Testnet3>>::new().iter(),
            Some((third_record, 1)),
            None,
            rng,
        )
        .unwrap();
        let second_execution = Transaction::execute(
            &vm,
            &caller_private_key,
            ("test_2.aleo", "init"),
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
}
