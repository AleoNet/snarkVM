// Copyright (C) 2019-2022 Aleo Systems Inc.
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

use crate::{
    atomic_write_batch,
    block::{Block, Transaction, Transactions, Transition},
    cast_ref,
    process,
    process::{Authorization, Deployment, Execution, Fee, Inclusion, InclusionAssignment, Process, Query},
    program::Program,
    store::{BlockStore, ConsensusStorage, ConsensusStore, ProgramStore, TransactionStore, TransitionStore},
    CallMetrics,
};
use console::{
    account::PrivateKey,
    network::prelude::*,
    program::{Identifier, Plaintext, ProgramID, Record, Response, Value},
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

        // Retrieve the transaction store.
        let transaction_store = store.transaction_store();
        // Load the deployments from the store.
        for transaction_id in transaction_store.deployment_ids() {
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
            Ok(_) => Ok(()),
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

    /// Returns the program store.
    #[inline]
    pub fn program_store(&self) -> &ProgramStore<N, C::ProgramStorage> {
        self.store.program_store()
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

    /// Starts an atomic batch write operation.
    pub fn start_atomic(&self) {
        self.store.start_atomic();
    }

    /// Checks if an atomic batch is in progress.
    pub fn is_atomic_in_progress(&self) -> bool {
        self.store.is_atomic_in_progress()
    }

    /// Aborts an atomic batch write operation.
    pub fn abort_atomic(&self) {
        self.store.abort_atomic();
    }

    /// Finishes an atomic batch write operation.
    pub fn finish_atomic(&self) -> Result<()> {
        self.store.finish_atomic()
    }
}

#[cfg(test)]
pub(crate) mod test_helpers {
    use super::*;
    use crate::{program::Program, Block, ConsensusMemory, Fee, Inclusion, Transition};
    use console::{
        account::{Address, ViewKey},
        network::Testnet3,
        program::Value,
    };

    use indexmap::IndexMap;
    use once_cell::sync::OnceCell;

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

record token:
    owner as address.private;
    gates as u64.private;
    amount as u64.private;

function mint:
    input r0 as address.private;
    input r1 as u64.private;
    cast r0 0u64 r1 into r2 as token.record;
    output r2 as token.record;

function compute:
    input r0 as message.private;
    input r1 as message.public;
    input r2 as message.private;
    input r3 as token.record;
    add r0.amount r1.amount into r4;
    cast r3.owner r3.gates r3.amount into r5 as token.record;
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

                // Prepare the additional fee.
                let credits = records.values().next().unwrap().decrypt(&caller_view_key).unwrap();
                let additional_fee = (credits, 10);

                // Initialize the VM.
                let vm = sample_vm();
                // Update the VM.
                vm.add_next_block(&genesis).unwrap();

                // Deploy.
                let transaction =
                    Transaction::deploy(&vm, &caller_private_key, &program, additional_fee, None, rng).unwrap();
                // Verify.
                assert!(vm.verify(&transaction));
                // Return the transaction.
                transaction
            })
            .clone()
    }

    pub(crate) fn sample_execution_transaction(rng: &mut TestRng) -> Transaction<CurrentNetwork> {
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

                // Authorize.
                let authorization = vm
                    .authorize(
                        &caller_private_key,
                        "credits.aleo",
                        "transfer",
                        [
                            Value::<CurrentNetwork>::Record(record),
                            Value::<CurrentNetwork>::from_str(&address.to_string()).unwrap(),
                            Value::<CurrentNetwork>::from_str("1u64").unwrap(),
                        ]
                        .into_iter(),
                        rng,
                    )
                    .unwrap();
                assert_eq!(authorization.len(), 1);

                // Execute.
                let transaction = Transaction::execute_authorization(&vm, authorization, None, rng).unwrap();
                // Verify.
                assert!(vm.verify(&transaction));
                // Return the transaction.
                transaction
            })
            .clone()
    }

    pub(crate) fn sample_fee() -> Fee<CurrentNetwork> {
        static INSTANCE: OnceCell<Fee<CurrentNetwork>> = OnceCell::new();
        INSTANCE
            .get_or_init(|| {
                let rng = &mut TestRng::default();

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
                Inclusion::verify_fee(&fee).unwrap();
                // Return the fee.
                fee
            })
            .clone()
    }
}
