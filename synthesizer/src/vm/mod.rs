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
pub use helpers::*;

mod authorize;
mod deploy;
mod execute;
mod finalize;
mod verify;

use crate::{cast_mut_ref, cast_ref, process};
use console::{
    account::{Address, PrivateKey},
    network::prelude::*,
    program::{Identifier, Literal, Locator, Plaintext, ProgramID, ProgramOwner, Record, Value},
    types::{Field, Group, U64},
};
use ledger_block::{
    Block,
    ConfirmedTransaction,
    Deployment,
    Execution,
    Fee,
    Header,
    Ratifications,
    Ratify,
    Rejected,
    Solutions,
    Transaction,
    Transactions,
};
use ledger_committee::Committee;
use ledger_query::Query;
use ledger_store::{
    atomic_finalize,
    BlockStore,
    ConsensusStorage,
    ConsensusStore,
    FinalizeMode,
    FinalizeStore,
    TransactionStorage,
    TransactionStore,
    TransitionStore,
};
use synthesizer_process::{Authorization, Process, Trace};
use synthesizer_program::{FinalizeGlobalState, FinalizeOperation, FinalizeStoreTrait, Program};

use aleo_std::prelude::{finish, lap, timer};
use indexmap::{IndexMap, IndexSet};
use lru::LruCache;
use parking_lot::{Mutex, RwLock};
use std::{num::NonZeroUsize, sync::Arc};

#[cfg(not(feature = "serial"))]
use rayon::prelude::*;

#[derive(Clone)]
pub struct VM<N: Network, C: ConsensusStorage<N>> {
    /// The process.
    process: Arc<RwLock<Process<N>>>,
    /// The VM store.
    store: ConsensusStore<N, C>,
    /// The lock to guarantee atomicity over calls to speculate and finalize.
    atomic_lock: Arc<Mutex<()>>,
    /// The lock for ensuring there is no concurrency when advancing blocks.
    block_lock: Arc<Mutex<()>>,
    /// A cache containing the list of recent partially-verified transactions.
    partially_verified_transactions: Arc<RwLock<LruCache<N::TransactionID, ()>>>,
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
                store.finalize_store().initialize_mapping(*credits.id(), *mapping.name())?;
            }
        }

        // A helper function to retrieve all the deployments.
        fn load_deployment_and_imports<N: Network, T: TransactionStorage<N>>(
            process: &Process<N>,
            transaction_store: &TransactionStore<N, T>,
            transaction_id: N::TransactionID,
        ) -> Result<Vec<(ProgramID<N>, Deployment<N>)>> {
            // Retrieve the deployment from the transaction ID.
            let deployment = match transaction_store.get_deployment(&transaction_id)? {
                Some(deployment) => deployment,
                None => bail!("Deployment transaction '{transaction_id}' is not found in storage."),
            };

            // Fetch the program from the deployment.
            let program = deployment.program();
            let program_id = program.id();

            // Return early if the program is already loaded.
            if process.contains_program(program_id) {
                return Ok(vec![]);
            }

            // Prepare a vector for the deployments.
            let mut deployments = vec![];

            // Iterate through the program imports.
            for import_program_id in program.imports().keys() {
                // Add the imports to the process if does not exist yet.
                if !process.contains_program(import_program_id) {
                    // Fetch the deployment transaction ID.
                    let Some(transaction_id) =
                        transaction_store.deployment_store().find_transaction_id_from_program_id(import_program_id)?
                    else {
                        bail!("Transaction ID for '{program_id}' is not found in storage.");
                    };

                    // Add the deployment and its imports found recursively.
                    deployments.extend_from_slice(&load_deployment_and_imports(
                        process,
                        transaction_store,
                        transaction_id,
                    )?);
                }
            }

            // Once all the imports have been included, add the parent deployment.
            deployments.push((*program_id, deployment));

            Ok(deployments)
        }

        // Retrieve the transaction store.
        let transaction_store = store.transaction_store();
        // Retrieve the list of deployment transaction IDs.
        let deployment_ids = transaction_store.deployment_transaction_ids().collect::<Vec<_>>();
        // Load the deployments from the store.
        for (i, chunk) in deployment_ids.chunks(256).enumerate() {
            debug!(
                "Loading deployments {}-{} (of {})...",
                i * 256,
                ((i + 1) * 256).min(deployment_ids.len()),
                deployment_ids.len()
            );
            let deployments = cfg_iter!(chunk)
                .map(|transaction_id| {
                    // Load the deployment and its imports.
                    load_deployment_and_imports(&process, transaction_store, **transaction_id)
                })
                .collect::<Result<Vec<_>>>()?;

            for (program_id, deployment) in deployments.iter().flatten() {
                // Load the deployment if it does not exist in the process yet.
                if !process.contains_program(program_id) {
                    process.load_deployment(deployment)?;
                }
            }
        }

        // Return the new VM.
        Ok(Self {
            process: Arc::new(RwLock::new(process)),
            store,
            atomic_lock: Arc::new(Mutex::new(())),
            block_lock: Arc::new(Mutex::new(())),
            partially_verified_transactions: Arc::new(RwLock::new(LruCache::new(
                NonZeroUsize::new(Transactions::<N>::MAX_TRANSACTIONS).unwrap(),
            ))),
        })
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

    /// Returns the partially-verified transactions.
    #[inline]
    pub fn partially_verified_transactions(&self) -> Arc<RwLock<LruCache<N::TransactionID, ()>>> {
        self.partially_verified_transactions.clone()
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
    /// Returns a new genesis block for a beacon chain.
    pub fn genesis_beacon<R: Rng + CryptoRng>(&self, private_key: &PrivateKey<N>, rng: &mut R) -> Result<Block<N>> {
        let private_keys = [*private_key, PrivateKey::new(rng)?, PrivateKey::new(rng)?, PrivateKey::new(rng)?];

        // Construct the committee members.
        let members = indexmap::indexmap! {
            Address::try_from(private_keys[0])? => (ledger_committee::MIN_VALIDATOR_STAKE, true),
            Address::try_from(private_keys[1])? => (ledger_committee::MIN_VALIDATOR_STAKE, true),
            Address::try_from(private_keys[2])? => (ledger_committee::MIN_VALIDATOR_STAKE, true),
            Address::try_from(private_keys[3])? => (ledger_committee::MIN_VALIDATOR_STAKE, true),
        };
        // Construct the committee.
        let committee = Committee::<N>::new_genesis(members)?;

        // Compute the remaining supply.
        let remaining_supply = N::STARTING_SUPPLY - (ledger_committee::MIN_VALIDATOR_STAKE * 4);
        // Construct the public balances.
        let public_balances = indexmap::indexmap! {
            Address::try_from(private_keys[0])? => remaining_supply / 4,
            Address::try_from(private_keys[1])? => remaining_supply / 4,
            Address::try_from(private_keys[2])? => remaining_supply / 4,
            Address::try_from(private_keys[3])? => remaining_supply / 4,
        };
        // Construct the bonded balances.
        let bonded_balances =
            committee.members().iter().map(|(address, (amount, _))| (*address, (*address, *amount))).collect();
        // Return the genesis block.
        self.genesis_quorum(private_key, committee, public_balances, bonded_balances, rng)
    }

    /// Returns a new genesis block for a quorum chain.
    pub fn genesis_quorum<R: Rng + CryptoRng>(
        &self,
        private_key: &PrivateKey<N>,
        committee: Committee<N>,
        public_balances: IndexMap<Address<N>, u64>,
        bonded_balances: IndexMap<Address<N>, (Address<N>, u64)>,
        rng: &mut R,
    ) -> Result<Block<N>> {
        // Retrieve the total stake.
        let total_stake = committee.total_stake();
        // Compute the account supply.
        let account_supply = public_balances
            .values()
            .try_fold(0u64, |acc, x| acc.checked_add(*x).ok_or(anyhow!("Invalid account supply")))?;
        // Compute the total supply.
        let total_supply = total_stake.checked_add(account_supply).ok_or_else(|| anyhow!("Invalid total supply"))?;
        // Ensure the total supply matches.
        ensure!(
            total_supply == N::STARTING_SUPPLY,
            "Invalid total supply. Found {total_supply}, expected {}",
            N::STARTING_SUPPLY
        );

        // Prepare the caller.
        let caller = Address::try_from(private_key)?;
        // Prepare the locator.
        let locator = ("credits.aleo", "transfer_public_to_private");
        // Prepare the amount for each call to the function.
        let amount = ledger_committee::MIN_VALIDATOR_STAKE;
        // Prepare the function inputs.
        let inputs = [caller.to_string(), format!("{amount}_u64")];

        // Prepare the ratifications.
        let ratifications =
            vec![Ratify::Genesis(Box::new(committee), Box::new(public_balances), Box::new(bonded_balances))];
        // Prepare the solutions.
        let solutions = Solutions::<N>::from(None); // The genesis block does not require solutions.
        // Prepare the aborted solution IDs.
        let aborted_solution_ids = vec![];
        // Prepare the transactions.
        let transactions = (0..Block::<N>::NUM_GENESIS_TRANSACTIONS)
            .map(|_| self.execute(private_key, locator, inputs.iter(), None, 0, None, rng))
            .collect::<Result<Vec<_>, _>>()?;

        // Construct the finalize state.
        let state = FinalizeGlobalState::new_genesis::<N>()?;
        // Speculate on the ratifications, solutions, and transactions.
        let (ratifications, transactions, aborted_transaction_ids, ratified_finalize_operations) =
            self.speculate(state, None, ratifications, &solutions, transactions.iter())?;
        ensure!(
            aborted_transaction_ids.is_empty(),
            "Failed to initialize a genesis block - found aborted transaction IDs"
        );

        // Prepare the block header.
        let header = Header::genesis(&ratifications, &transactions, ratified_finalize_operations)?;
        // Prepare the previous block hash.
        let previous_hash = N::BlockHash::default();

        // Construct the block.
        let block = Block::new_beacon(
            private_key,
            previous_hash,
            header,
            ratifications,
            solutions,
            aborted_solution_ids,
            transactions,
            aborted_transaction_ids,
            rng,
        )?;
        // Ensure the block is valid genesis block.
        match block.is_genesis() {
            true => Ok(block),
            false => bail!("Failed to initialize a genesis block"),
        }
    }

    /// Adds the given block into the VM.
    #[inline]
    pub fn add_next_block(&self, block: &Block<N>) -> Result<()> {
        // Acquire the block lock, which is needed to ensure this function is not called concurrently.
        // Note: This lock must be held for the entire scope of this function.
        let _block_lock = self.block_lock.lock();

        // Construct the finalize state.
        let state = FinalizeGlobalState::new::<N>(
            block.round(),
            block.height(),
            block.cumulative_weight(),
            block.cumulative_proof_target(),
            block.previous_hash(),
        )?;

        // Pause the atomic writes, so that both the insertion and finalization belong to a single batch.
        #[cfg(feature = "rocks")]
        self.block_store().pause_atomic_writes()?;

        // First, insert the block.
        self.block_store().insert(block)?;
        // Next, finalize the transactions.
        match self.finalize(state, block.ratifications(), block.solutions(), block.transactions()) {
            Ok(_ratified_finalize_operations) => {
                // Unpause the atomic writes, executing the ones queued from block insertion and finalization.
                #[cfg(feature = "rocks")]
                self.block_store().unpause_atomic_writes::<false>()?;
                Ok(())
            }
            Err(finalize_error) => {
                if cfg!(feature = "rocks") {
                    // Clear all pending atomic operations so that unpausing the atomic writes
                    // doesn't execute any of the queued storage operations.
                    self.block_store().abort_atomic();
                    self.finalize_store().abort_atomic();
                    // Disable the atomic batch override.
                    // Note: This call is guaranteed to succeed (without error), because `DISCARD_BATCH == true`.
                    self.block_store().unpause_atomic_writes::<true>()?;
                    // Rollback the Merkle tree.
                    self.block_store().remove_last_n_from_tree_only(1).map_err(|removal_error| {
                        // Log the finalize error.
                        error!("Failed to finalize block {} - {finalize_error}", block.height());
                        // Return the removal error.
                        removal_error
                    })?;
                } else {
                    // Rollback the block.
                    self.block_store().remove_last_n(1).map_err(|removal_error| {
                        // Log the finalize error.
                        error!("Failed to finalize block {} - {finalize_error}", block.height());
                        // Return the removal error.
                        removal_error
                    })?;
                }
                // Return the finalize error.
                Err(finalize_error)
            }
        }
    }
}

#[cfg(test)]
pub(crate) mod test_helpers {
    use super::*;
    use console::{
        account::{Address, ViewKey},
        network::MainnetV0,
        program::Value,
        types::Field,
    };
    use ledger_block::{Block, Header, Metadata, Transition};
    use ledger_store::helpers::memory::ConsensusMemory;
    use synthesizer_program::Program;

    use indexmap::IndexMap;
    use once_cell::sync::OnceCell;
    use std::borrow::Borrow;
    use synthesizer_snark::VerifyingKey;

    pub(crate) type CurrentNetwork = MainnetV0;

    /// Samples a new finalize state.
    pub(crate) fn sample_finalize_state(block_height: u32) -> FinalizeGlobalState {
        FinalizeGlobalState::from(block_height as u64, block_height, [0u8; 32])
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
                vm.genesis_beacon(&caller_private_key, rng).unwrap()
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
    key as address.public;
    value as u64.public;

record token:
    owner as address.private;
    amount as u64.private;

function initialize:
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
                let credits = Some(records.values().next().unwrap().decrypt(&caller_view_key).unwrap());

                // Initialize the VM.
                let vm = sample_vm();
                // Update the VM.
                vm.add_next_block(&genesis).unwrap();

                // Deploy.
                let transaction = vm.deploy(&caller_private_key, &program, credits, 10, None, rng).unwrap();
                // Verify.
                vm.check_transaction(&transaction, None, rng).unwrap();
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
                let inputs =
                    [Value::<CurrentNetwork>::Record(record), Value::<CurrentNetwork>::from_str("1u64").unwrap()]
                        .into_iter();

                // Authorize.
                let authorization = vm.authorize(&caller_private_key, "credits.aleo", "split", inputs, rng).unwrap();
                assert_eq!(authorization.len(), 1);

                // Construct the execute transaction.
                let transaction = vm.execute_authorization(authorization, None, None, rng).unwrap();
                // Verify.
                vm.check_transaction(&transaction, None, rng).unwrap();
                // Return the transaction.
                transaction
            })
            .clone()
    }

    pub(crate) fn sample_execution_transaction_with_private_fee(rng: &mut TestRng) -> Transaction<CurrentNetwork> {
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
                let record = Some(records.values().next().unwrap().decrypt(&caller_view_key).unwrap());

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

                // Execute.
                let transaction = vm
                    .execute(&caller_private_key, ("credits.aleo", "transfer_public"), inputs, record, 0, None, rng)
                    .unwrap();
                // Verify.
                vm.check_transaction(&transaction, None, rng).unwrap();
                // Return the transaction.
                transaction
            })
            .clone()
    }

    pub(crate) fn sample_execution_transaction_with_public_fee(rng: &mut TestRng) -> Transaction<CurrentNetwork> {
        static INSTANCE: OnceCell<Transaction<CurrentNetwork>> = OnceCell::new();
        INSTANCE
            .get_or_init(|| {
                // Initialize a new caller.
                let caller_private_key = crate::vm::test_helpers::sample_genesis_private_key(rng);
                let address = Address::try_from(&caller_private_key).unwrap();

                // Initialize the genesis block.
                let genesis = crate::vm::test_helpers::sample_genesis_block(rng);

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

                // Execute.
                let transaction_without_fee = vm
                    .execute(&caller_private_key, ("credits.aleo", "transfer_public"), inputs, None, 0, None, rng)
                    .unwrap();
                let execution = transaction_without_fee.execution().unwrap().clone();

                // Authorize the fee.
                let authorization = vm
                    .authorize_fee_public(
                        &caller_private_key,
                        10_000_000,
                        100,
                        execution.to_execution_id().unwrap(),
                        rng,
                    )
                    .unwrap();
                // Compute the fee.
                let fee = vm.execute_fee_authorization(authorization, None, rng).unwrap();

                // Construct the transaction.
                let transaction = Transaction::from_execution(execution, Some(fee)).unwrap();
                // Verify.
                vm.check_transaction(&transaction, None, rng).unwrap();
                // Return the transaction.
                transaction
            })
            .clone()
    }

    pub fn sample_next_block<R: Rng + CryptoRng>(
        vm: &VM<MainnetV0, ConsensusMemory<MainnetV0>>,
        private_key: &PrivateKey<MainnetV0>,
        transactions: &[Transaction<MainnetV0>],
        rng: &mut R,
    ) -> Result<Block<MainnetV0>> {
        // Get the most recent block.
        let block_hash =
            vm.block_store().get_block_hash(*vm.block_store().heights().max().unwrap().borrow()).unwrap().unwrap();
        let previous_block = vm.block_store().get_block(&block_hash).unwrap().unwrap();

        // Construct the new block header.
        let (ratifications, transactions, aborted_transaction_ids, ratified_finalize_operations) =
            vm.speculate(sample_finalize_state(1), None, vec![], &None.into(), transactions.iter())?;
        assert!(aborted_transaction_ids.is_empty());

        // Construct the metadata associated with the block.
        let metadata = Metadata::new(
            MainnetV0::ID,
            previous_block.round() + 1,
            previous_block.height() + 1,
            0,
            0,
            MainnetV0::GENESIS_COINBASE_TARGET,
            MainnetV0::GENESIS_PROOF_TARGET,
            previous_block.last_coinbase_target(),
            previous_block.last_coinbase_timestamp(),
            MainnetV0::GENESIS_TIMESTAMP + 1,
        )?;

        let header = Header::from(
            vm.block_store().current_state_root(),
            transactions.to_transactions_root().unwrap(),
            transactions.to_finalize_root(ratified_finalize_operations).unwrap(),
            ratifications.to_ratifications_root().unwrap(),
            Field::zero(),
            Field::zero(),
            metadata,
        )?;

        // Construct the new block.
        Block::new_beacon(
            private_key,
            previous_block.hash(),
            header,
            ratifications,
            None.into(),
            vec![],
            transactions,
            aborted_transaction_ids,
            rng,
        )
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
                0,
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
                0,
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
                0,
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
    key as field.public;
    value as field.public;
function init:
    async init into r0;
    output r0 as test_program_1.aleo/init.future;
finalize init:
    set 0field into map_0[0field];
function getter:
    async getter into r0;
    output r0 as test_program_1.aleo/getter.future;
finalize getter:
    get map_0[0field] into r0;
        ";
        let second_program = r"
program test_program_2.aleo;
mapping map_0:
    key as field.public;
    value as field.public;
function init:
    async init into r0;
    output r0 as test_program_2.aleo/init.future;
finalize init:
    set 0field into map_0[0field];
function getter:
    async getter into r0;
    output r0 as test_program_2.aleo/getter.future;
finalize getter:
    get map_0[0field] into r0;
        ";
        let first_deployment = vm
            .deploy(&caller_private_key, &Program::from_str(first_program).unwrap(), Some(first_record), 1, None, rng)
            .unwrap();
        let second_deployment = vm
            .deploy(&caller_private_key, &Program::from_str(second_program).unwrap(), Some(second_record), 1, None, rng)
            .unwrap();
        let deployment_block =
            sample_next_block(&vm, &caller_private_key, &[first_deployment, second_deployment], rng).unwrap();
        vm.add_next_block(&deployment_block).unwrap();

        // Execute the programs.
        let first_execution = vm
            .execute(
                &caller_private_key,
                ("test_program_1.aleo", "init"),
                Vec::<Value<MainnetV0>>::new().iter(),
                Some(third_record),
                1,
                None,
                rng,
            )
            .unwrap();
        let second_execution = vm
            .execute(
                &caller_private_key,
                ("test_program_2.aleo", "init"),
                Vec::<Value<MainnetV0>>::new().iter(),
                Some(fourth_record),
                1,
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
        let genesis = vm.genesis_beacon(&caller_private_key, rng).unwrap();
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
        let deployment_1 = vm
            .deploy(&caller_private_key, &Program::from_str(program_1).unwrap(), Some(record_0), 0, None, rng)
            .unwrap();

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
        let deployment_2 = vm
            .deploy(&caller_private_key, &Program::from_str(program_2).unwrap(), Some(record_1), 0, None, rng)
            .unwrap();

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
        let deployment_3 = vm
            .deploy(&caller_private_key, &Program::from_str(program_3).unwrap(), Some(record_2), 0, None, rng)
            .unwrap();

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
        let deployment_4 = vm
            .deploy(&caller_private_key, &Program::from_str(program_4).unwrap(), Some(record_3), 0, None, rng)
            .unwrap();

        // Deploy the third and fourth program together.
        let deployment_block =
            sample_next_block(&vm, &caller_private_key, &[deployment_3.clone(), deployment_4.clone()], rng).unwrap();
        vm.add_next_block(&deployment_block).unwrap();

        // Sanity check the ordering of the deployment transaction IDs from storage.
        {
            let deployment_transaction_ids =
                vm.transaction_store().deployment_transaction_ids().map(|id| *id).collect::<Vec<_>>();
            // This assert check is here to ensure that we are properly loading imports even though any order will work for `VM::from`.
            // Note: `deployment_transaction_ids` is sorted lexicographically by transaction ID, so the order may change if we update internal methods.
            assert_eq!(
                deployment_transaction_ids,
                vec![deployment_1.id(), deployment_2.id(), deployment_3.id(), deployment_4.id()],
                "Update me if serialization has changed"
            );
        }

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
        let deployment = vm.deploy(&caller_private_key, &program, Some(record_0), 1, None, rng).unwrap();
        vm.add_next_block(&sample_next_block(&vm, &caller_private_key, &[deployment], rng).unwrap()).unwrap();

        // Execute the programs.
        let inputs = [
            Value::<MainnetV0>::Record(record_1),
            Value::<MainnetV0>::from_str(&address.to_string()).unwrap(),
            Value::<MainnetV0>::from_str("10u64").unwrap(),
        ];
        let execution = vm
            .execute(
                &caller_private_key,
                ("test_multiple_external_calls.aleo", "multitransfer"),
                inputs.into_iter(),
                Some(record_2),
                1,
                None,
                rng,
            )
            .unwrap();
        vm.add_next_block(&sample_next_block(&vm, &caller_private_key, &[execution], rng).unwrap()).unwrap();
    }

    #[test]
    fn test_nested_deployment_with_assert() {
        let rng = &mut TestRng::default();

        // Initialize a private key.
        let private_key = sample_genesis_private_key(rng);

        // Initialize the genesis block.
        let genesis = sample_genesis_block(rng);

        // Initialize the VM.
        let vm = sample_vm();
        // Update the VM.
        vm.add_next_block(&genesis).unwrap();

        // Deploy the base program.
        let program = Program::from_str(
            r"
program child_program.aleo;

function check:
    input r0 as field.private;
    assert.eq r0 123456789123456789123456789123456789123456789123456789field;
        ",
        )
        .unwrap();

        let deployment = vm.deploy(&private_key, &program, None, 0, None, rng).unwrap();
        assert!(vm.check_transaction(&deployment, None, rng).is_ok());
        vm.add_next_block(&sample_next_block(&vm, &private_key, &[deployment], rng).unwrap()).unwrap();

        // Check that program is deployed.
        assert!(vm.contains_program(&ProgramID::from_str("child_program.aleo").unwrap()));

        // Deploy the program that calls the program from the previous layer.
        let program = Program::from_str(
            r"
import child_program.aleo;

program parent_program.aleo;

function check:
    input r0 as field.private;
    call child_program.aleo/check r0;
        ",
        )
        .unwrap();

        let deployment = vm.deploy(&private_key, &program, None, 0, None, rng).unwrap();
        assert!(vm.check_transaction(&deployment, None, rng).is_ok());
        vm.add_next_block(&sample_next_block(&vm, &private_key, &[deployment], rng).unwrap()).unwrap();

        // Check that program is deployed.
        assert!(vm.contains_program(&ProgramID::from_str("parent_program.aleo").unwrap()));
    }

    #[test]
    fn test_deployment_with_external_records() {
        let rng = &mut TestRng::default();

        // Initialize a private key.
        let private_key = sample_genesis_private_key(rng);

        // Initialize the genesis block.
        let genesis = sample_genesis_block(rng);

        // Initialize the VM.
        let vm = sample_vm();
        // Update the VM.
        vm.add_next_block(&genesis).unwrap();

        // Deploy the program.
        let program = Program::from_str(
            r"
import credits.aleo;
program test_program.aleo;

function transfer:
    input r0 as credits.aleo/credits.record;
    input r1 as u64.private;
    input r2 as u64.private;
    input r3 as [address; 10u32].private;
    call credits.aleo/transfer_private r0 r3[0u32] r1 into r4 r5;
    call credits.aleo/transfer_private r5 r3[0u32] r2 into r6 r7;
",
        )
        .unwrap();

        let deployment = vm.deploy(&private_key, &program, None, 0, None, rng).unwrap();
        assert!(vm.check_transaction(&deployment, None, rng).is_ok());
        vm.add_next_block(&sample_next_block(&vm, &private_key, &[deployment], rng).unwrap()).unwrap();

        // Check that program is deployed.
        assert!(vm.contains_program(&ProgramID::from_str("test_program.aleo").unwrap()));
    }

    #[test]
    fn test_deployment_synthesis_overload() {
        let rng = &mut TestRng::default();

        // Initialize a private key.
        let private_key = sample_genesis_private_key(rng);

        // Initialize the genesis block.
        let genesis = sample_genesis_block(rng);

        // Initialize the VM.
        let vm = sample_vm();
        // Update the VM.
        vm.add_next_block(&genesis).unwrap();

        // Deploy the base program.
        let program = Program::from_str(
            r"
program synthesis_overload.aleo;

function do:
    input r0 as [[u128; 32u32]; 2u32].private;
    hash.sha3_256 r0 into r1 as field;
    output r1 as field.public;",
        )
        .unwrap();

        // Create the deployment transaction.
        let deployment = vm.deploy(&private_key, &program, None, 0, None, rng).unwrap();

        // Verify the deployment transaction. It should fail because there are too many constraints.
        assert!(vm.check_transaction(&deployment, None, rng).is_err());
    }

    #[test]
    fn test_deployment_synthesis_overreport() {
        let rng = &mut TestRng::default();

        // Initialize a private key.
        let private_key = sample_genesis_private_key(rng);

        // Initialize the genesis block.
        let genesis = sample_genesis_block(rng);

        // Initialize the VM.
        let vm = sample_vm();
        // Update the VM.
        vm.add_next_block(&genesis).unwrap();

        // Deploy the base program.
        let program = Program::from_str(
            r"
program synthesis_overreport.aleo;

function do:
    input r0 as u32.private;
    add r0 r0 into r1;
    output r1 as u32.public;",
        )
        .unwrap();

        // Create the deployment transaction.
        let transaction = vm.deploy(&private_key, &program, None, 0, None, rng).unwrap();

        // Destructure the deployment transaction.
        let Transaction::Deploy(_, program_owner, deployment, fee) = transaction else {
            panic!("Expected a deployment transaction");
        };

        // Increase the number of constraints in the verifying keys.
        let mut vks_with_overreport = Vec::with_capacity(deployment.verifying_keys().len());
        for (id, (vk, cert)) in deployment.verifying_keys() {
            let mut vk = vk.deref().clone();
            vk.circuit_info.num_constraints += 1;
            let vk = VerifyingKey::new(Arc::new(vk));
            vks_with_overreport.push((*id, (vk, cert.clone())));
        }

        // Each additional constraint costs 25 microcredits, so we need to increase the fee by 25 microcredits.
        let required_fee = *fee.base_amount().unwrap() + 25;
        // Authorize a new fee.
        let fee_authorization = vm
            .authorize_fee_public(&private_key, required_fee, 0, deployment.as_ref().to_deployment_id().unwrap(), rng)
            .unwrap();
        // Compute the fee.
        let fee = vm.execute_fee_authorization(fee_authorization, None, rng).unwrap();

        // Create a new deployment transaction with the overreported verifying keys.
        let adjusted_deployment =
            Deployment::new(deployment.edition(), deployment.program().clone(), vks_with_overreport).unwrap();
        let adjusted_transaction = Transaction::from_deployment(program_owner, adjusted_deployment, fee).unwrap();

        // Verify the deployment transaction. It should error when certificate checking for constraint count mismatch.
        let res = vm.check_transaction(&adjusted_transaction, None, rng);
        assert!(res.is_err());
    }

    #[test]
    #[should_panic]
    fn test_deployment_synthesis_underreport() {
        let rng = &mut TestRng::default();

        // Initialize a private key.
        let private_key = sample_genesis_private_key(rng);

        // Initialize the genesis block.
        let genesis = sample_genesis_block(rng);

        // Initialize the VM.
        let vm = sample_vm();
        // Update the VM.
        vm.add_next_block(&genesis).unwrap();

        // Deploy the base program.
        let program = Program::from_str(
            r"
program synthesis_underreport.aleo;

function do:
    input r0 as u32.private;
    add r0 r0 into r1;
    output r1 as u32.public;",
        )
        .unwrap();

        // Create the deployment transaction.
        let transaction = vm.deploy(&private_key, &program, None, 0, None, rng).unwrap();

        // Destructure the deployment transaction.
        let Transaction::Deploy(txid, program_owner, deployment, fee) = transaction else {
            panic!("Expected a deployment transaction");
        };

        // Decrease the number of constraints in the verifying keys.
        let mut vks_with_underreport = Vec::with_capacity(deployment.verifying_keys().len());
        for (id, (vk, cert)) in deployment.verifying_keys() {
            let mut vk = vk.deref().clone();
            vk.circuit_info.num_constraints -= 2;
            let vk = VerifyingKey::new(Arc::new(vk));
            vks_with_underreport.push((*id, (vk, cert.clone())));
        }

        // Create a new deployment transaction with the underreported verifying keys.
        let adjusted_deployment =
            Deployment::new(deployment.edition(), deployment.program().clone(), vks_with_underreport).unwrap();
        let adjusted_transaction = Transaction::Deploy(txid, program_owner, Box::new(adjusted_deployment), fee);

        // Verify the deployment transaction. It should panic when enforcing the first constraint over the vk limit.
        let _ = vm.check_transaction(&adjusted_transaction, None, rng);
    }

    #[test]
    // #[ignore]
    fn test_deployment_memory_overload() {
        const NUM_DEPLOYMENTS: usize = 31;

        let rng = &mut TestRng::default();

        // Initialize a private key.
        let private_key = sample_genesis_private_key(rng);

        // Initialize a view key.
        let view_key = ViewKey::try_from(&private_key).unwrap();

        // Initialize the genesis block.
        let genesis = sample_genesis_block(rng);

        // Initialize the VM.
        let vm = sample_vm();
        // Update the VM.
        vm.add_next_block(&genesis).unwrap();

        // Deploy the base program.
        let program = Program::from_str(
            r"
program program_layer_0.aleo;

mapping m:
    key as u8.public;
    value as u32.public;

function do:
    input r0 as u32.public;

    hash.sha3_256 r0 into r1 as field; 
    hash.sha3_256 r1 into r2 as field; 
    hash.sha3_256 r2 into r3 as field; 
    hash.sha3_256 r3 into r4 as field; 
    hash.sha3_256 r4 into r5 as field; 
    hash.sha3_256 r5 into r6 as field; 
    hash.psd8 r6 into r7 as field; 
    hash.psd8 r7 into r8 as field; 
    hash.psd8 r8 into r9 as field; 
    hash.psd8 r9 into r10 as field; 
    hash.psd8 r10 into r11 as field; 
    hash.psd8 r11 into r12 as field; 
    hash.psd8 r12 into r13 as field; 
    hash.psd8 r13 into r14 as field; 
    hash.psd8 r14 into r15 as field; 
    hash.psd8 r15 into r16 as field; 
    hash.psd8 r16 into r17 as field; 
    hash.psd8 r17 into r18 as field; 
    hash.psd8 r18 into r19 as field; 
    hash.psd8 r19 into r20 as field; 
    hash.psd8 r20 into r21 as field; 
    hash.psd8 r21 into r22 as field; 
    hash.psd8 r22 into r23 as field; 
    hash.psd8 r23 into r24 as field; 
    hash.psd8 r24 into r25 as field; 
    hash.psd8 r25 into r26 as field; 
    hash.psd8 r26 into r27 as field; 
    hash.psd8 r27 into r28 as field; 
    hash.psd8 r28 into r29 as field; 
    hash.psd8 r29 into r30 as field; 
    hash.psd8 r30 into r31 as field; 
    hash.psd8 r31 into r32 as field; 
    hash.psd8 r32 into r33 as field; 
    hash.psd8 r33 into r34 as field; 
    hash.psd8 r34 into r35 as field; 
    hash.psd8 r35 into r36 as field; 
    hash.psd8 r36 into r37 as field; 
    hash.psd8 r37 into r38 as field; 
    hash.psd8 r38 into r39 as field; 
    hash.psd8 r39 into r40 as field; 
    hash.psd8 r40 into r41 as field; 
    hash.psd8 r41 into r42 as field; 
    hash.psd8 r42 into r43 as field; 
    hash.psd8 r43 into r44 as field; 
    hash.psd8 r44 into r45 as field; 
    hash.psd8 r45 into r46 as field; 
    hash.psd8 r46 into r47 as field; 
    hash.psd8 r47 into r48 as field; 
    hash.psd8 r48 into r49 as field; 
    hash.psd8 r49 into r50 as field; 
    hash.psd8 r50 into r51 as field; 
    hash.psd8 r51 into r52 as field; 
    hash.psd8 r52 into r53 as field; 
    hash.psd8 r53 into r54 as field; 
    hash.psd8 r54 into r55 as field; 
    hash.psd8 r55 into r56 as field; 
    hash.psd8 r56 into r57 as field; 
    hash.psd8 r57 into r58 as field; 
    hash.psd8 r58 into r59 as field; 
    hash.psd8 r59 into r60 as field; 
    hash.psd8 r60 into r61 as field; 
    hash.psd8 r61 into r62 as field; 
    hash.psd8 r62 into r63 as field; 
    hash.psd8 r63 into r64 as field; 
    hash.psd8 r64 into r65 as field; 
    hash.psd8 r65 into r66 as field; 
    hash.psd8 r66 into r67 as field; 
    hash.psd8 r67 into r68 as field; 
    hash.psd8 r68 into r69 as field; 
    hash.psd8 r69 into r70 as field; 
    hash.psd8 r70 into r71 as field; 
    hash.psd8 r71 into r72 as field; 
    hash.psd8 r72 into r73 as field; 
    hash.psd8 r73 into r74 as field; 
    hash.psd8 r74 into r75 as field; 
    hash.psd8 r75 into r76 as field; 
    hash.psd8 r76 into r77 as field; 
    hash.psd8 r77 into r78 as field; 
    hash.psd8 r78 into r79 as field; 
    hash.psd8 r79 into r80 as field; 
    hash.psd8 r80 into r81 as field; 
    hash.psd8 r81 into r82 as field; 
    hash.psd8 r82 into r83 as field; 
    hash.psd8 r83 into r84 as field; 
    hash.psd8 r84 into r85 as field; 
    hash.psd8 r85 into r86 as field; 
    hash.psd8 r86 into r87 as field; 
    hash.psd8 r87 into r88 as field; 
    hash.psd8 r88 into r89 as field; 
    hash.psd8 r89 into r90 as field; 
    hash.psd8 r90 into r91 as field; 
    hash.psd8 r91 into r92 as field; 
    hash.psd8 r92 into r93 as field; 
    hash.psd8 r93 into r94 as field; 
    hash.psd8 r94 into r95 as field; 
    hash.psd8 r95 into r96 as field; 

    async do r0 into r97;
    output r97 as program_layer_0.aleo/do.future;

finalize do:
    input r0 as u32.public;
    set r0 into m[0u8];",
        )
        .unwrap();

        let deployment = vm.deploy(&private_key, &program, None, 0, None, rng).unwrap();
        vm.add_next_block(&sample_next_block(&vm, &private_key, &[deployment], rng).unwrap()).unwrap();

        // For each layer, deploy a program that calls the program from the previous layer.
        for i in 1..NUM_DEPLOYMENTS {
            let mut program_string = String::new();
            // Add the import statements.
            for j in 0..i {
                program_string.push_str(&format!("import program_layer_{}.aleo;\n", j));
            }
            // Add the program body.
            program_string.push_str(&format!(
                "program program_layer_{i}.aleo;

mapping m:
    key as u8.public;
    value as u32.public;

function do:
    input r0 as u32.public;
    call program_layer_{prev}.aleo/do r0 into r1;
    async do r0 r1 into r2;

    hash.sha3_256 r0 into r3 as field; 
    hash.sha3_256 r1 into r4 as field; 
    hash.sha3_256 r2 into r5 as field; 
    hash.sha3_256 r3 into r6 as field; 
    hash.sha3_256 r4 into r7 as field; 
    hash.sha3_256 r5 into r8 as field; 
    hash.psd8 r8 into r9 as field; 
    hash.psd8 r9 into r10 as field; 
    hash.psd8 r10 into r11 as field; 
    hash.psd8 r11 into r12 as field; 
    hash.psd8 r12 into r13 as field; 
    hash.psd8 r13 into r14 as field; 
    hash.psd8 r14 into r15 as field; 
    hash.psd8 r15 into r16 as field; 
    hash.psd8 r16 into r17 as field; 
    hash.psd8 r17 into r18 as field; 
    hash.psd8 r18 into r19 as field; 
    hash.psd8 r19 into r20 as field; 
    hash.psd8 r20 into r21 as field; 
    hash.psd8 r21 into r22 as field; 
    hash.psd8 r22 into r23 as field; 
    hash.psd8 r23 into r24 as field; 
    hash.psd8 r24 into r25 as field; 
    hash.psd8 r25 into r26 as field; 
    hash.psd8 r26 into r27 as field; 
    hash.psd8 r27 into r28 as field; 
    hash.psd8 r28 into r29 as field; 
    hash.psd8 r29 into r30 as field; 
    hash.psd8 r30 into r31 as field; 
    hash.psd8 r31 into r32 as field; 
    hash.psd8 r32 into r33 as field; 
    hash.psd8 r33 into r34 as field; 
    hash.psd8 r34 into r35 as field; 
    hash.psd8 r35 into r36 as field; 
    hash.psd8 r36 into r37 as field; 
    hash.psd8 r37 into r38 as field; 
    hash.psd8 r38 into r39 as field; 
    hash.psd8 r39 into r40 as field; 
    hash.psd8 r40 into r41 as field; 
    hash.psd8 r41 into r42 as field; 
    hash.psd8 r42 into r43 as field; 
    hash.psd8 r43 into r44 as field; 
    hash.psd8 r44 into r45 as field; 
    hash.psd8 r45 into r46 as field; 
    hash.psd8 r46 into r47 as field; 
    hash.psd8 r47 into r48 as field; 
    hash.psd8 r48 into r49 as field; 
    hash.psd8 r49 into r50 as field; 
    hash.psd8 r50 into r51 as field; 
    hash.psd8 r51 into r52 as field; 
    hash.psd8 r52 into r53 as field; 
    hash.psd8 r53 into r54 as field; 
    hash.psd8 r54 into r55 as field; 
    hash.psd8 r55 into r56 as field; 
    hash.psd8 r56 into r57 as field; 
    hash.psd8 r57 into r58 as field; 
    hash.psd8 r58 into r59 as field; 
    hash.psd8 r59 into r60 as field; 
    hash.psd8 r60 into r61 as field; 
    hash.psd8 r61 into r62 as field; 
    hash.psd8 r62 into r63 as field; 
    hash.psd8 r63 into r64 as field; 
    hash.psd8 r64 into r65 as field; 
    hash.psd8 r65 into r66 as field; 
    hash.psd8 r66 into r67 as field; 
    hash.psd8 r67 into r68 as field; 
    hash.psd8 r68 into r69 as field; 
    hash.psd8 r69 into r70 as field; 
    hash.psd8 r70 into r71 as field; 
    hash.psd8 r71 into r72 as field; 
    hash.psd8 r72 into r73 as field; 
    hash.psd8 r73 into r74 as field; 
    hash.psd8 r74 into r75 as field; 
    hash.psd8 r75 into r76 as field; 
    hash.psd8 r76 into r77 as field; 
    hash.psd8 r77 into r78 as field; 
    hash.psd8 r78 into r79 as field; 
    hash.psd8 r79 into r80 as field; 
    hash.psd8 r80 into r81 as field; 
    hash.psd8 r81 into r82 as field; 
    hash.psd8 r82 into r83 as field; 
    hash.psd8 r83 into r84 as field; 
    hash.psd8 r84 into r85 as field; 
    hash.psd8 r85 into r86 as field; 
    hash.psd8 r86 into r87 as field; 
    hash.psd8 r87 into r88 as field; 
    hash.psd8 r88 into r89 as field; 
    hash.psd8 r89 into r90 as field; 
    hash.psd8 r90 into r91 as field; 
    hash.psd8 r91 into r92 as field; 
    hash.psd8 r92 into r93 as field; 
    hash.psd8 r93 into r94 as field; 
    hash.psd8 r94 into r95 as field; 
    hash.psd8 r95 into r96 as field; 

    output r2 as program_layer_{i}.aleo/do.future;

finalize do:
    input r0 as u32.public;
    input r1 as program_layer_{prev}.aleo/do.future;
    await r1;
    set r0 into m[0u8];",
                prev = i - 1
            ));
            // Construct the program.
            let program = Program::from_str(&program_string).unwrap();

            // Deploy the program.
            let deployment = vm.deploy(&private_key, &program, None, 0, None, rng).unwrap();

            vm.add_next_block(&sample_next_block(&vm, &private_key, &[deployment], rng).unwrap()).unwrap();
        }

        // Fetch the unspent records.
        let records = genesis.transitions().cloned().flat_map(Transition::into_records).collect::<IndexMap<_, _>>();
        trace!("Unspent Records:\n{:#?}", records);

        // Select a record to spend.
        let record = Some(records.values().next().unwrap().decrypt(&view_key).unwrap());

        // Prepare the inputs.
        let inputs = [Value::<CurrentNetwork>::from_str("1u32").unwrap()].into_iter();

        // Execute.
        let transaction1 =
            vm.execute(&private_key, ("program_layer_0.aleo", "do"), inputs.clone(), record.clone(), 0, None, rng).unwrap();
        let transaction2 =
            vm.execute(&private_key, ("program_layer_1.aleo", "do"), inputs.clone(), record.clone(), 0, None, rng).unwrap();
        let transaction3 =
            vm.execute(&private_key, ("program_layer_2.aleo", "do"), inputs.clone(), record.clone(), 0, None, rng).unwrap();
        let transaction4 =
            vm.execute(&private_key, ("program_layer_3.aleo", "do"), inputs.clone(), record.clone(), 0, None, rng).unwrap();
        let transaction5 =
            vm.execute(&private_key, ("program_layer_4.aleo", "do"), inputs.clone(), record.clone(), 0, None, rng).unwrap();
        let transaction6 =
            vm.execute(&private_key, ("program_layer_5.aleo", "do"), inputs.clone(), record.clone(), 0, None, rng).unwrap();
        let transaction7 =
            vm.execute(&private_key, ("program_layer_6.aleo", "do"), inputs.clone(), record.clone(), 0, None, rng).unwrap();
        let transaction31 =
            vm.execute(&private_key, ("program_layer_30.aleo", "do"), inputs.clone(), record.clone(), 0, None, rng).unwrap();

        // Verify.
        vm.check_transaction(&transaction1, None, rng).unwrap();
        vm.check_transaction(&transaction2, None, rng).unwrap();
        vm.check_transaction(&transaction3, None, rng).unwrap();
        vm.check_transaction(&transaction4, None, rng).unwrap();
        vm.check_transaction(&transaction5, None, rng).unwrap();
        vm.check_transaction(&transaction6, None, rng).unwrap();
        vm.check_transaction(&transaction7, None, rng).unwrap();
        vm.check_transaction(&transaction31, None, rng).unwrap();
    }

//     #[test]
//     fn test_large_finalize() {
//         let rng = &mut TestRng::default();

//         // Initialize a private key.
//         let private_key = sample_genesis_private_key(rng);

//         // Initialize a view key.
//         let view_key = ViewKey::try_from(&private_key).unwrap();

//         // Initialize the genesis block.
//         let genesis = sample_genesis_block(rng);

//         // Initialize the VM.
//         let vm = sample_vm();
//         // Update the VM.
//         vm.add_next_block(&genesis).unwrap();

//         // Deploy the base program.
//         let program = Program::from_str(
//             r"
// program program_layer_0.aleo;

// function do:
//     async do into r0;
//     output r0 as program_layer_0.aleo/do.future;

// finalize do:
//     cast  254u8 251u8 44u8 77u8 25u8 254u8 254u8 253u8 224u8 2u8 114u8 253u8 23u8 2u8 177u8 134u8 into r0 as [u8; 16u32];
//     cast  r0 r0 r0 r0 r0 r0 r0 r0 r0 r0 r0 r0 r0 r0 r0 r0 into r1 as [[u8; 16u32]; 16u32];
//     cast  r1 r1 r1 r1 r1 r1 r1 r1 into r2 as [[[u8; 16u32]; 16u32]; 8u32];
//     hash.bhp256 r2 into r3 as field;
//     hash.bhp256 r2 into r4 as field;
//     hash.bhp256 r2 into r5 as field;
//     hash.bhp256 r2 into r6 as field;
//     hash.bhp256 r2 into r7 as field;
//     hash.bhp256 r2 into r8 as field;
//     hash.bhp256 r2 into r9 as field;
//     hash.bhp256 r2 into r10 as field;
//     hash.bhp256 r2 into r11 as field;
//     hash.bhp256 r2 into r12 as field;
//     hash.bhp256 r2 into r13 as field;
//     hash.bhp256 r2 into r14 as field;
//     hash.bhp256 r2 into r15 as field;
//     hash.bhp256 r2 into r16 as field;
//     hash.bhp256 r2 into r17 as field;
//     hash.bhp256 r2 into r18 as field;
//     hash.bhp256 r2 into r19 as field;
//     hash.bhp256 r2 into r20 as field;
//     hash.bhp256 r2 into r21 as field;
//     hash.bhp256 r2 into r22 as field;
//     hash.bhp256 r2 into r23 as field;
//     hash.bhp256 r2 into r24 as field;
//     hash.bhp256 r2 into r25 as field;
//     hash.bhp256 r2 into r26 as field;
//     hash.bhp256 r2 into r27 as field;
//     hash.bhp256 r2 into r28 as field;
//     hash.bhp256 r2 into r29 as field;
//     hash.bhp256 r2 into r30 as field;
//     hash.bhp256 r2 into r31 as field;
//     hash.bhp256 r2 into r32 as field;
//     hash.bhp256 r2 into r33 as field;
//     hash.bhp256 r2 into r34 as field;
//     hash.bhp256 r2 into r35 as field;
//     hash.bhp256 r2 into r36 as field;
//     hash.bhp256 r2 into r37 as field;
//     hash.bhp256 r2 into r38 as field;
//     hash.bhp256 r2 into r39 as field;
//     hash.bhp256 r2 into r40 as field;
//     hash.bhp256 r2 into r41 as field;
//     hash.bhp256 r2 into r42 as field;
//     hash.bhp256 r2 into r43 as field;
//     hash.bhp256 r2 into r44 as field;
//     hash.bhp256 r2 into r45 as field;
//     hash.bhp256 r2 into r46 as field;
//     hash.bhp256 r2 into r47 as field;
//     hash.bhp256 r2 into r48 as field;
//     hash.bhp256 r2 into r49 as field;
//     hash.bhp256 r2 into r50 as field;
//     hash.bhp256 r2 into r51 as field;
//     hash.bhp256 r2 into r52 as field;
//     hash.bhp256 r2 into r53 as field;
//     hash.bhp256 r2 into r54 as field;
//     hash.bhp256 r2 into r55 as field;
//     hash.bhp256 r2 into r56 as field;
//     hash.bhp256 r2 into r57 as field;
//     hash.bhp256 r2 into r58 as field;
//     hash.bhp256 r2 into r59 as field;
//     hash.bhp256 r2 into r60 as field;
//     hash.bhp256 r2 into r61 as field;
//     hash.bhp256 r2 into r62 as field;
//     hash.bhp256 r2 into r63 as field;
//     hash.bhp256 r2 into r64 as field;
//     hash.bhp256 r2 into r65 as field;
//     hash.bhp256 r2 into r66 as field;
//     hash.bhp256 r2 into r67 as field;
//     hash.bhp256 r2 into r68 as field;
//     hash.bhp256 r2 into r69 as field;
//     hash.bhp256 r2 into r70 as field;
//     hash.bhp256 r2 into r71 as field;
//     hash.bhp256 r2 into r72 as field;
//     hash.bhp256 r2 into r73 as field;
//     hash.bhp256 r2 into r74 as field;
//     hash.bhp256 r2 into r75 as field;
//     hash.bhp256 r2 into r76 as field;
//     hash.bhp256 r2 into r77 as field;
//     hash.bhp256 r2 into r78 as field;
//     hash.bhp256 r2 into r79 as field;
//     hash.bhp256 r2 into r80 as field;
//     hash.bhp256 r2 into r81 as field;
//     hash.bhp256 r2 into r82 as field;
//     hash.bhp256 r2 into r83 as field;
//     hash.bhp256 r2 into r84 as field;
//     hash.bhp256 r2 into r85 as field;
//     hash.bhp256 r2 into r86 as field;
//     hash.bhp256 r2 into r87 as field;
//     hash.bhp256 r2 into r88 as field;
//     hash.bhp256 r2 into r89 as field;
//     hash.bhp256 r2 into r90 as field;
//     hash.bhp256 r2 into r91 as field;
//     hash.bhp256 r2 into r92 as field;
//     hash.bhp256 r2 into r93 as field;
//     hash.bhp256 r2 into r94 as field;
//     hash.bhp256 r2 into r95 as field;
//     hash.bhp256 r2 into r96 as field;
//     hash.bhp256 r2 into r97 as field;
//     hash.bhp256 r2 into r98 as field;
//     hash.bhp256 r2 into r99 as field;
//     hash.bhp256 r2 into r100 as field;
//     hash.bhp256 r2 into r101 as field;
//     hash.bhp256 r2 into r102 as field;
//     hash.bhp256 r2 into r103 as field;
//     hash.bhp256 r2 into r104 as field;
//     hash.bhp256 r2 into r105 as field;
//     hash.bhp256 r2 into r106 as field;
//     hash.bhp256 r2 into r107 as field;
//     hash.bhp256 r2 into r108 as field;
//     hash.bhp256 r2 into r109 as field;
//     hash.bhp256 r2 into r110 as field;
//     hash.bhp256 r2 into r111 as field;
//     hash.bhp256 r2 into r112 as field;
//     hash.bhp256 r2 into r113 as field;
//     hash.bhp256 r2 into r114 as field;
//     hash.bhp256 r2 into r115 as field;
//     hash.bhp256 r2 into r116 as field;
//     hash.bhp256 r2 into r117 as field;
//     hash.bhp256 r2 into r118 as field;
//     hash.bhp256 r2 into r119 as field;
//     hash.bhp256 r2 into r120 as field;
//     hash.bhp256 r2 into r121 as field;
//     hash.bhp256 r2 into r122 as field;
//     hash.bhp256 r2 into r123 as field;
//     hash.bhp256 r2 into r124 as field;
//     hash.bhp256 r2 into r125 as field;
//     hash.bhp256 r2 into r126 as field;
//     hash.bhp256 r2 into r127 as field;
//     hash.bhp256 r2 into r128 as field;
//     hash.bhp256 r2 into r129 as field;
//     hash.bhp256 r2 into r130 as field;
//     hash.bhp256 r2 into r131 as field;
//     hash.bhp256 r2 into r132 as field;
//     hash.bhp256 r2 into r133 as field;
//     hash.bhp256 r2 into r134 as field;
//     hash.bhp256 r2 into r135 as field;
//     hash.bhp256 r2 into r136 as field;
//     hash.bhp256 r2 into r137 as field;
//     hash.bhp256 r2 into r138 as field;
//     hash.bhp256 r2 into r139 as field;
//     hash.bhp256 r2 into r140 as field;
//     hash.bhp256 r2 into r141 as field;
//     hash.bhp256 r2 into r142 as field;
//     hash.bhp256 r2 into r143 as field;
//     hash.bhp256 r2 into r144 as field;
//     hash.bhp256 r2 into r145 as field;
//     hash.bhp256 r2 into r146 as field;
//     hash.bhp256 r2 into r147 as field;
//     hash.bhp256 r2 into r148 as field;
//     hash.bhp256 r2 into r149 as field;
//     hash.bhp256 r2 into r150 as field;
//     hash.bhp256 r2 into r151 as field;
//     hash.bhp256 r2 into r152 as field;
//     hash.bhp256 r2 into r153 as field;
//     hash.bhp256 r2 into r154 as field;
//     hash.bhp256 r2 into r155 as field;
//     hash.bhp256 r2 into r156 as field;
//     hash.bhp256 r2 into r157 as field;
//     hash.bhp256 r2 into r158 as field;
//     hash.bhp256 r2 into r159 as field;
//     hash.bhp256 r2 into r160 as field;
//     hash.bhp256 r2 into r161 as field;
//     hash.bhp256 r2 into r162 as field;
//     hash.bhp256 r2 into r163 as field;
//     hash.bhp256 r2 into r164 as field;
//     hash.bhp256 r2 into r165 as field;
//     hash.bhp256 r2 into r166 as field;
//     hash.bhp256 r2 into r167 as field;
//     hash.bhp256 r2 into r168 as field;
//     hash.bhp256 r2 into r169 as field;
//     hash.bhp256 r2 into r170 as field;
//     hash.bhp256 r2 into r171 as field;
//     hash.bhp256 r2 into r172 as field;
//     hash.bhp256 r2 into r173 as field;
//     hash.bhp256 r2 into r174 as field;
//     hash.bhp256 r2 into r175 as field;
//     hash.bhp256 r2 into r176 as field;
//     hash.bhp256 r2 into r177 as field;
//     hash.bhp256 r2 into r178 as field;
//     hash.bhp256 r2 into r179 as field;
//     hash.bhp256 r2 into r180 as field;
//     hash.bhp256 r2 into r181 as field;
//     hash.bhp256 r2 into r182 as field;
//     hash.bhp256 r2 into r183 as field;
//     hash.bhp256 r2 into r184 as field;
//     hash.bhp256 r2 into r185 as field;
//     hash.bhp256 r2 into r186 as field;
//     hash.bhp256 r2 into r187 as field;
//     hash.bhp256 r2 into r188 as field;
//     hash.bhp256 r2 into r189 as field;
//     hash.bhp256 r2 into r190 as field;
//     hash.bhp256 r2 into r191 as field;
//     hash.bhp256 r2 into r192 as field;
//     hash.bhp256 r2 into r193 as field;
//     hash.bhp256 r2 into r194 as field;
//     hash.bhp256 r2 into r195 as field;
//     hash.bhp256 r2 into r196 as field;
//     hash.bhp256 r2 into r197 as field;
//     hash.bhp256 r2 into r198 as field;
//     hash.bhp256 r2 into r199 as field;
//     hash.bhp256 r2 into r200 as field;
//     hash.bhp256 r2 into r201 as field;
//     hash.bhp256 r2 into r202 as field;
//     hash.bhp256 r2 into r203 as field;
//     hash.bhp256 r2 into r204 as field;
//     hash.bhp256 r2 into r205 as field;
//     hash.bhp256 r2 into r206 as field;
//     hash.bhp256 r2 into r207 as field;
//     hash.bhp256 r2 into r208 as field;
//     hash.bhp256 r2 into r209 as field;
//     hash.bhp256 r2 into r210 as field;
//     hash.bhp256 r2 into r211 as field;
//     hash.bhp256 r2 into r212 as field;
//     hash.bhp256 r2 into r213 as field;
//     hash.bhp256 r2 into r214 as field;
//     hash.bhp256 r2 into r215 as field;
//     hash.bhp256 r2 into r216 as field;
//     hash.bhp256 r2 into r217 as field;
//     hash.bhp256 r2 into r218 as field;
//     hash.bhp256 r2 into r219 as field;
//     hash.bhp256 r2 into r220 as field;
//     hash.bhp256 r2 into r221 as field;
//     hash.bhp256 r2 into r222 as field;
//     hash.bhp256 r2 into r223 as field;
//     hash.bhp256 r2 into r224 as field;
//     hash.bhp256 r2 into r225 as field;
//     hash.bhp256 r2 into r226 as field;
//     hash.bhp256 r2 into r227 as field;
//     hash.bhp256 r2 into r228 as field;
//     hash.bhp256 r2 into r229 as field;
//     hash.bhp256 r2 into r230 as field;
//     hash.bhp256 r2 into r231 as field;
//     hash.bhp256 r2 into r232 as field;
//     hash.bhp256 r2 into r233 as field;
//     hash.bhp256 r2 into r234 as field;
//     hash.bhp256 r2 into r235 as field;
//     hash.bhp256 r2 into r236 as field;
//     hash.bhp256 r2 into r237 as field;
//     hash.bhp256 r2 into r238 as field;
//     hash.bhp256 r2 into r239 as field;
//     hash.bhp256 r2 into r240 as field;
//     hash.bhp256 r2 into r241 as field;
//     hash.bhp256 r2 into r242 as field;
//     hash.bhp256 r2 into r243 as field;
//     hash.bhp256 r2 into r244 as field;
//     hash.bhp256 r2 into r245 as field;
//     hash.bhp256 r2 into r246 as field;
//     hash.bhp256 r2 into r247 as field;
//     hash.bhp256 r2 into r248 as field;
//     hash.bhp256 r2 into r249 as field;
//     hash.bhp256 r2 into r250 as field;
//     hash.bhp256 r2 into r251 as field;
//     hash.bhp256 r2 into r252 as field;
//     hash.bhp256 r2 into r253 as field;
//     hash.bhp256 r2 into r254 as field;
//     hash.bhp256 r2 into r255 as field;
//     hash.bhp256 r2 into r256 as field;
//     hash.bhp256 r2 into r257 as field;
//     hash.bhp256 r2 into r258 as field;
//     hash.bhp256 r2 into r259 as field;
//     hash.bhp256 r2 into r260 as field;
//     hash.bhp256 r2 into r261 as field;
//     hash.bhp256 r2 into r262 as field;
//     hash.bhp256 r2 into r263 as field;
//     hash.bhp256 r2 into r264 as field;
//     hash.bhp256 r2 into r265 as field;
//     hash.bhp256 r2 into r266 as field;
//     hash.bhp256 r2 into r267 as field;
//     hash.bhp256 r2 into r268 as field;
//     hash.bhp256 r2 into r269 as field;
//     hash.bhp256 r2 into r270 as field;
//     hash.bhp256 r2 into r271 as field;
//     hash.bhp256 r2 into r272 as field;
//     hash.bhp256 r2 into r273 as field;
//     hash.bhp256 r2 into r274 as field;
//     hash.bhp256 r2 into r275 as field;
//     hash.bhp256 r2 into r276 as field;
//     hash.bhp256 r2 into r277 as field;
//     hash.bhp256 r2 into r278 as field;
//     hash.bhp256 r2 into r279 as field;
//     hash.bhp256 r2 into r280 as field;
//     hash.bhp256 r2 into r281 as field;
//     hash.bhp256 r2 into r282 as field;
//     hash.bhp256 r2 into r283 as field;
//     hash.bhp256 r2 into r284 as field;
//     hash.bhp256 r2 into r285 as field;
//     hash.bhp256 r2 into r286 as field;
//     hash.bhp256 r2 into r287 as field;
//     hash.bhp256 r2 into r288 as field;
//     hash.bhp256 r2 into r289 as field;
//     hash.bhp256 r2 into r290 as field;
//     hash.bhp256 r2 into r291 as field;
//     hash.bhp256 r2 into r292 as field;
//     hash.bhp256 r2 into r293 as field;
//     hash.bhp256 r2 into r294 as field;
//     hash.bhp256 r2 into r295 as field;
//     hash.bhp256 r2 into r296 as field;
//     hash.bhp256 r2 into r297 as field;
//     hash.bhp256 r2 into r298 as field;
//     hash.bhp256 r2 into r299 as field;
//     hash.bhp256 r2 into r300 as field;
//     hash.bhp256 r2 into r301 as field;
//     hash.bhp256 r2 into r302 as field;
//     hash.bhp256 r2 into r303 as field;
//     hash.bhp256 r2 into r304 as field;
//     hash.bhp256 r2 into r305 as field;
//     hash.bhp256 r2 into r306 as field;
//     hash.bhp256 r2 into r307 as field;
//     hash.bhp256 r2 into r308 as field;
//     hash.bhp256 r2 into r309 as field;
//     hash.bhp256 r2 into r310 as field;
//     hash.bhp256 r2 into r311 as field;
//     hash.bhp256 r2 into r312 as field;
//     hash.bhp256 r2 into r313 as field;
//     hash.bhp256 r2 into r314 as field;
//     hash.bhp256 r2 into r315 as field;
//     hash.bhp256 r2 into r316 as field;
//     hash.bhp256 r2 into r317 as field;
//     hash.bhp256 r2 into r318 as field;
//     hash.bhp256 r2 into r319 as field;
//     hash.bhp256 r2 into r320 as field;
//     hash.bhp256 r2 into r321 as field;
//     hash.bhp256 r2 into r322 as field;
//     hash.bhp256 r2 into r323 as field;
//     hash.bhp256 r2 into r324 as field;
//     hash.bhp256 r2 into r325 as field;
//     hash.bhp256 r2 into r326 as field;
//     hash.bhp256 r2 into r327 as field;
//     hash.bhp256 r2 into r328 as field;
//     hash.bhp256 r2 into r329 as field;
//     hash.bhp256 r2 into r330 as field;
//     hash.bhp256 r2 into r331 as field;
//     hash.bhp256 r2 into r332 as field;
//     hash.bhp256 r2 into r333 as field;
//     hash.bhp256 r2 into r334 as field;
//     hash.bhp256 r2 into r335 as field;
//     hash.bhp256 r2 into r336 as field;
//     hash.bhp256 r2 into r337 as field;
//     hash.bhp256 r2 into r338 as field;
//     hash.bhp256 r2 into r339 as field;
//     hash.bhp256 r2 into r340 as field;
//     hash.bhp256 r2 into r341 as field;
//     hash.bhp256 r2 into r342 as field;
//     hash.bhp256 r2 into r343 as field;
//     hash.bhp256 r2 into r344 as field;
//     hash.bhp256 r2 into r345 as field;
//     hash.bhp256 r2 into r346 as field;
//     hash.bhp256 r2 into r347 as field;
//     hash.bhp256 r2 into r348 as field;
//     hash.bhp256 r2 into r349 as field;
//     hash.bhp256 r2 into r350 as field;
//     hash.bhp256 r2 into r351 as field;
//     hash.bhp256 r2 into r352 as field;
//     hash.bhp256 r2 into r353 as field;
//     hash.bhp256 r2 into r354 as field;
//     hash.bhp256 r2 into r355 as field;
//     hash.bhp256 r2 into r356 as field;
//     hash.bhp256 r2 into r357 as field;
//     hash.bhp256 r2 into r358 as field;
//     hash.bhp256 r2 into r359 as field;
//     hash.bhp256 r2 into r360 as field;
//     hash.bhp256 r2 into r361 as field;
//     hash.bhp256 r2 into r362 as field;
//     hash.bhp256 r2 into r363 as field;
//     hash.bhp256 r2 into r364 as field;
//     hash.bhp256 r2 into r365 as field;
//     hash.bhp256 r2 into r366 as field;
//     hash.bhp256 r2 into r367 as field;
//     hash.bhp256 r2 into r368 as field;
//     hash.bhp256 r2 into r369 as field;
//     hash.bhp256 r2 into r370 as field;
//     hash.bhp256 r2 into r371 as field;
//     hash.bhp256 r2 into r372 as field;
//     hash.bhp256 r2 into r373 as field;
//     hash.bhp256 r2 into r374 as field;
//     hash.bhp256 r2 into r375 as field;
//     hash.bhp256 r2 into r376 as field;
//     hash.bhp256 r2 into r377 as field;
//     hash.bhp256 r2 into r378 as field;
//     hash.bhp256 r2 into r379 as field;
//     hash.bhp256 r2 into r380 as field;
//     hash.bhp256 r2 into r381 as field;
//     hash.bhp256 r2 into r382 as field;
//     hash.bhp256 r2 into r383 as field;
//     hash.bhp256 r2 into r384 as field;
//     hash.bhp256 r2 into r385 as field;
//     hash.bhp256 r2 into r386 as field;
//     hash.bhp256 r2 into r387 as field;
//     hash.bhp256 r2 into r388 as field;
//     hash.bhp256 r2 into r389 as field;
//     hash.bhp256 r2 into r390 as field;
//     hash.bhp256 r2 into r391 as field;
//     hash.bhp256 r2 into r392 as field;
//     hash.bhp256 r2 into r393 as field;
//     hash.bhp256 r2 into r394 as field;
//     hash.bhp256 r2 into r395 as field;
//     hash.bhp256 r2 into r396 as field;
//     hash.bhp256 r2 into r397 as field;
//     hash.bhp256 r2 into r398 as field;
//     hash.bhp256 r2 into r399 as field;
//     hash.bhp256 r2 into r400 as field;
//     hash.bhp256 r2 into r401 as field;
//     hash.bhp256 r2 into r402 as field;
//     hash.bhp256 r2 into r403 as field;
//     hash.bhp256 r2 into r404 as field;
//     hash.bhp256 r2 into r405 as field;
//     hash.bhp256 r2 into r406 as field;
//     hash.bhp256 r2 into r407 as field;
//     hash.bhp256 r2 into r408 as field;
//     hash.bhp256 r2 into r409 as field;
//     hash.bhp256 r2 into r410 as field;
//     hash.bhp256 r2 into r411 as field;
//     hash.bhp256 r2 into r412 as field;
//     hash.bhp256 r2 into r413 as field;
//     hash.bhp256 r2 into r414 as field;
//     hash.bhp256 r2 into r415 as field;
//     hash.bhp256 r2 into r416 as field;
//     hash.bhp256 r2 into r417 as field;
//     hash.bhp256 r2 into r418 as field;
//     hash.bhp256 r2 into r419 as field;
//     hash.bhp256 r2 into r420 as field;
//     hash.bhp256 r2 into r421 as field;
//     hash.bhp256 r2 into r422 as field;
//     hash.bhp256 r2 into r423 as field;
//     hash.bhp256 r2 into r424 as field;
//     hash.bhp256 r2 into r425 as field;
//     hash.bhp256 r2 into r426 as field;
//     hash.bhp256 r2 into r427 as field;
//     hash.bhp256 r2 into r428 as field;
//     hash.bhp256 r2 into r429 as field;
//     hash.bhp256 r2 into r430 as field;
//     hash.bhp256 r2 into r431 as field;
//     hash.bhp256 r2 into r432 as field;
//     hash.bhp256 r2 into r433 as field;
//     hash.bhp256 r2 into r434 as field;
//     hash.bhp256 r2 into r435 as field;
//     hash.bhp256 r2 into r436 as field;
//     hash.bhp256 r2 into r437 as field;
//     hash.bhp256 r2 into r438 as field;
//     hash.bhp256 r2 into r439 as field;
//     hash.bhp256 r2 into r440 as field;
//     hash.bhp256 r2 into r441 as field;
//     hash.bhp256 r2 into r442 as field;
//     hash.bhp256 r2 into r443 as field;
//     hash.bhp256 r2 into r444 as field;
//     hash.bhp256 r2 into r445 as field;
//     hash.bhp256 r2 into r446 as field;
//     hash.bhp256 r2 into r447 as field;
//     hash.bhp256 r2 into r448 as field;
//     hash.bhp256 r2 into r449 as field;
//     hash.bhp256 r2 into r450 as field;
//     hash.bhp256 r2 into r451 as field;
//     hash.bhp256 r2 into r452 as field;
//     hash.bhp256 r2 into r453 as field;
//     hash.bhp256 r2 into r454 as field;
//     hash.bhp256 r2 into r455 as field;
//     hash.bhp256 r2 into r456 as field;
//     hash.bhp256 r2 into r457 as field;
//     hash.bhp256 r2 into r458 as field;
//     hash.bhp256 r2 into r459 as field;
//     hash.bhp256 r2 into r460 as field;
//     hash.bhp256 r2 into r461 as field;
//     hash.bhp256 r2 into r462 as field;
//     hash.bhp256 r2 into r463 as field;
//     hash.bhp256 r2 into r464 as field;
//     hash.bhp256 r2 into r465 as field;
//     hash.bhp256 r2 into r466 as field;
//     hash.bhp256 r2 into r467 as field;
//     hash.bhp256 r2 into r468 as field;
//     hash.bhp256 r2 into r469 as field;
//     hash.bhp256 r2 into r470 as field;
//     hash.bhp256 r2 into r471 as field;
//     hash.bhp256 r2 into r472 as field;
//     hash.bhp256 r2 into r473 as field;
//     hash.bhp256 r2 into r474 as field;
//     hash.bhp256 r2 into r475 as field;
//     hash.bhp256 r2 into r476 as field;
//     hash.bhp256 r2 into r477 as field;
//     hash.bhp256 r2 into r478 as field;
//     hash.bhp256 r2 into r479 as field;
//     hash.bhp256 r2 into r480 as field;
//     hash.bhp256 r2 into r481 as field;
//     hash.bhp256 r2 into r482 as field;
//     hash.bhp256 r2 into r483 as field;
//     hash.bhp256 r2 into r484 as field;
//     hash.bhp256 r2 into r485 as field;
//     hash.bhp256 r2 into r486 as field;
//     hash.bhp256 r2 into r487 as field;
//     hash.bhp256 r2 into r488 as field;
//     hash.bhp256 r2 into r489 as field;
//     hash.bhp256 r2 into r490 as field;
//     hash.bhp256 r2 into r491 as field;
//     hash.bhp256 r2 into r492 as field;
//     hash.bhp256 r2 into r493 as field;
//     hash.bhp256 r2 into r494 as field;
//     hash.bhp256 r2 into r495 as field;
//     hash.bhp256 r2 into r496 as field;
//     hash.bhp256 r2 into r497 as field;
//     hash.bhp256 r2 into r498 as field;
//     hash.bhp256 r2 into r499 as field;
//     hash.bhp256 r2 into r500 as field;
//     hash.bhp256 r2 into r501 as field;
//     hash.bhp256 r2 into r502 as field;
//     hash.bhp256 r2 into r503 as field;
//     hash.bhp256 r2 into r504 as field;
//     hash.bhp256 r2 into r505 as field;
//     hash.bhp256 r2 into r506 as field;
//     hash.bhp256 r2 into r507 as field;
//     hash.bhp256 r2 into r508 as field;
//     hash.bhp256 r2 into r509 as field;
//     hash.bhp256 r2 into r510 as field;
//     hash.bhp256 r2 into r511 as field;
//     hash.bhp256 r2 into r512 as field;
//     hash.bhp256 r2 into r513 as field;
//     hash.bhp256 r2 into r514 as field;
//     hash.bhp256 r2 into r515 as field;
//     hash.bhp256 r2 into r516 as field;
//     hash.bhp256 r2 into r517 as field;
//     hash.bhp256 r2 into r518 as field;
//     hash.bhp256 r2 into r519 as field;
//     hash.bhp256 r2 into r520 as field;
//     hash.bhp256 r2 into r521 as field;
//     hash.bhp256 r2 into r522 as field;
//     hash.bhp256 r2 into r523 as field;
//     hash.bhp256 r2 into r524 as field;
//     hash.bhp256 r2 into r525 as field;
//     hash.bhp256 r2 into r526 as field;
//     hash.bhp256 r2 into r527 as field;
//     hash.bhp256 r2 into r528 as field;
//     hash.bhp256 r2 into r529 as field;
//     hash.bhp256 r2 into r530 as field;
//     hash.bhp256 r2 into r531 as field;
//     hash.bhp256 r2 into r532 as field;
//     hash.bhp256 r2 into r533 as field;
//     hash.bhp256 r2 into r534 as field;
//     hash.bhp256 r2 into r535 as field;
//     hash.bhp256 r2 into r536 as field;
//     hash.bhp256 r2 into r537 as field;
//     hash.bhp256 r2 into r538 as field;
//     hash.bhp256 r2 into r539 as field;
//     hash.bhp256 r2 into r540 as field;
//     hash.bhp256 r2 into r541 as field;
//     hash.bhp256 r2 into r542 as field;
//     hash.bhp256 r2 into r543 as field;
//     hash.bhp256 r2 into r544 as field;
//     hash.bhp256 r2 into r545 as field;
//     hash.bhp256 r2 into r546 as field;
//     hash.bhp256 r2 into r547 as field;
//     hash.bhp256 r2 into r548 as field;
//     hash.bhp256 r2 into r549 as field;
//     hash.bhp256 r2 into r550 as field;
//     hash.bhp256 r2 into r551 as field;
//     hash.bhp256 r2 into r552 as field;
//     hash.bhp256 r2 into r553 as field;
//     hash.bhp256 r2 into r554 as field;
//     hash.bhp256 r2 into r555 as field;
//     hash.bhp256 r2 into r556 as field;
//     hash.bhp256 r2 into r557 as field;
//     hash.bhp256 r2 into r558 as field;
//     hash.bhp256 r2 into r559 as field;
//     hash.bhp256 r2 into r560 as field;
//     hash.bhp256 r2 into r561 as field;
//     hash.bhp256 r2 into r562 as field;
//     hash.bhp256 r2 into r563 as field;
//     hash.bhp256 r2 into r564 as field;
//     hash.bhp256 r2 into r565 as field;
//     hash.bhp256 r2 into r566 as field;
//     hash.bhp256 r2 into r567 as field;
//     hash.bhp256 r2 into r568 as field;
//     hash.bhp256 r2 into r569 as field;
//     hash.bhp256 r2 into r570 as field;
//     hash.bhp256 r2 into r571 as field;
//     hash.bhp256 r2 into r572 as field;
//     hash.bhp256 r2 into r573 as field;
//     hash.bhp256 r2 into r574 as field;
//     hash.bhp256 r2 into r575 as field;
//     hash.bhp256 r2 into r576 as field;
//     hash.bhp256 r2 into r577 as field;
//     hash.bhp256 r2 into r578 as field;
//     hash.bhp256 r2 into r579 as field;
//     hash.bhp256 r2 into r580 as field;
//     hash.bhp256 r2 into r581 as field;
//     hash.bhp256 r2 into r582 as field;
//     hash.bhp256 r2 into r583 as field;
//     hash.bhp256 r2 into r584 as field;
//     hash.bhp256 r2 into r585 as field;
//     hash.bhp256 r2 into r586 as field;
//     hash.bhp256 r2 into r587 as field;
//     hash.bhp256 r2 into r588 as field;
//     hash.bhp256 r2 into r589 as field;
//     hash.bhp256 r2 into r590 as field;
//     hash.bhp256 r2 into r591 as field;
//     hash.bhp256 r2 into r592 as field;
//     hash.bhp256 r2 into r593 as field;
//     hash.bhp256 r2 into r594 as field;
//     hash.bhp256 r2 into r595 as field;
//     hash.bhp256 r2 into r596 as field;
//     hash.bhp256 r2 into r597 as field;
//     hash.bhp256 r2 into r598 as field;
//     hash.bhp256 r2 into r599 as field;
//     hash.bhp256 r2 into r600 as field;
//     hash.bhp256 r2 into r601 as field;
//     hash.bhp256 r2 into r602 as field;
//     hash.bhp256 r2 into r603 as field;
//     hash.bhp256 r2 into r604 as field;
//     hash.bhp256 r2 into r605 as field;
//     hash.bhp256 r2 into r606 as field;
//     hash.bhp256 r2 into r607 as field;
//     hash.bhp256 r2 into r608 as field;
//     hash.bhp256 r2 into r609 as field;
//     hash.bhp256 r2 into r610 as field;
//     hash.bhp256 r2 into r611 as field;
//     hash.bhp256 r2 into r612 as field;
//     hash.bhp256 r2 into r613 as field;
//     hash.bhp256 r2 into r614 as field;
//     hash.bhp256 r2 into r615 as field;
//     hash.bhp256 r2 into r616 as field;
//     hash.bhp256 r2 into r617 as field;
//     hash.bhp256 r2 into r618 as field;
//     hash.bhp256 r2 into r619 as field;
//     hash.bhp256 r2 into r620 as field;
//     hash.bhp256 r2 into r621 as field;
//     hash.bhp256 r2 into r622 as field;
//     hash.bhp256 r2 into r623 as field;
//     hash.bhp256 r2 into r624 as field;
//     hash.bhp256 r2 into r625 as field;
//     hash.bhp256 r2 into r626 as field;
//     hash.bhp256 r2 into r627 as field;
//     hash.bhp256 r2 into r628 as field;
//     hash.bhp256 r2 into r629 as field;
//     hash.bhp256 r2 into r630 as field;
//     hash.bhp256 r2 into r631 as field;
//     hash.bhp256 r2 into r632 as field;
//     hash.bhp256 r2 into r633 as field;
//     hash.bhp256 r2 into r634 as field;
//     hash.bhp256 r2 into r635 as field;
//     hash.bhp256 r2 into r636 as field;
//     hash.bhp256 r2 into r637 as field;
//     hash.bhp256 r2 into r638 as field;
//     hash.bhp256 r2 into r639 as field;
//     hash.bhp256 r2 into r640 as field;
//     hash.bhp256 r2 into r641 as field;
//     hash.bhp256 r2 into r642 as field;
//     hash.bhp256 r2 into r643 as field;
//     hash.bhp256 r2 into r644 as field;
//     hash.bhp256 r2 into r645 as field;
//     hash.bhp256 r2 into r646 as field;
//     hash.bhp256 r2 into r647 as field;
//     hash.bhp256 r2 into r648 as field;
//     hash.bhp256 r2 into r649 as field;
//     hash.bhp256 r2 into r650 as field;
//     hash.bhp256 r2 into r651 as field;
//     hash.bhp256 r2 into r652 as field;
//     hash.bhp256 r2 into r653 as field;
//     hash.bhp256 r2 into r654 as field;
//     hash.bhp256 r2 into r655 as field;
//     hash.bhp256 r2 into r656 as field;
//     hash.bhp256 r2 into r657 as field;
//     hash.bhp256 r2 into r658 as field;
//     hash.bhp256 r2 into r659 as field;
//     hash.bhp256 r2 into r660 as field;
//     hash.bhp256 r2 into r661 as field;
//     hash.bhp256 r2 into r662 as field;
//     hash.bhp256 r2 into r663 as field;
//     hash.bhp256 r2 into r664 as field;
//     hash.bhp256 r2 into r665 as field;
//     hash.bhp256 r2 into r666 as field;
//     hash.bhp256 r2 into r667 as field;
//     hash.bhp256 r2 into r668 as field;
//     hash.bhp256 r2 into r669 as field;
//     hash.bhp256 r2 into r670 as field;
//     hash.bhp256 r2 into r671 as field;
//     hash.bhp256 r2 into r672 as field;
//     hash.bhp256 r2 into r673 as field;
//     hash.bhp256 r2 into r674 as field;
//     hash.bhp256 r2 into r675 as field;
//     hash.bhp256 r2 into r676 as field;
//     hash.bhp256 r2 into r677 as field;
//     hash.bhp256 r2 into r678 as field;
//     hash.bhp256 r2 into r679 as field;
//     hash.bhp256 r2 into r680 as field;
//     hash.bhp256 r2 into r681 as field;
//     hash.bhp256 r2 into r682 as field;
//     hash.bhp256 r2 into r683 as field;
//     hash.bhp256 r2 into r684 as field;
//     hash.bhp256 r2 into r685 as field;
//     hash.bhp256 r2 into r686 as field;
//     hash.bhp256 r2 into r687 as field;
//     hash.bhp256 r2 into r688 as field;
//     hash.bhp256 r2 into r689 as field;
//     hash.bhp256 r2 into r690 as field;
//     hash.bhp256 r2 into r691 as field;
//     hash.bhp256 r2 into r692 as field;
//     hash.bhp256 r2 into r693 as field;
//     hash.bhp256 r2 into r694 as field;
//     hash.bhp256 r2 into r695 as field;
//     hash.bhp256 r2 into r696 as field;
//     hash.bhp256 r2 into r697 as field;
//     hash.bhp256 r2 into r698 as field;
//     hash.bhp256 r2 into r699 as field;
//     hash.bhp256 r2 into r700 as field;
//     hash.bhp256 r2 into r701 as field;
//     hash.bhp256 r2 into r702 as field;
//     hash.bhp256 r2 into r703 as field;
//     hash.bhp256 r2 into r704 as field;
//     hash.bhp256 r2 into r705 as field;
//     hash.bhp256 r2 into r706 as field;
//     hash.bhp256 r2 into r707 as field;
//     hash.bhp256 r2 into r708 as field;
//     hash.bhp256 r2 into r709 as field;
//     hash.bhp256 r2 into r710 as field;
//     hash.bhp256 r2 into r711 as field;
//     hash.bhp256 r2 into r712 as field;
//     hash.bhp256 r2 into r713 as field;
//     hash.bhp256 r2 into r714 as field;
//     hash.bhp256 r2 into r715 as field;
//     hash.bhp256 r2 into r716 as field;
//     hash.bhp256 r2 into r717 as field;
//     hash.bhp256 r2 into r718 as field;
//     hash.bhp256 r2 into r719 as field;
//     hash.bhp256 r2 into r720 as field;
//     hash.bhp256 r2 into r721 as field;
//     hash.bhp256 r2 into r722 as field;
//     hash.bhp256 r2 into r723 as field;
//     hash.bhp256 r2 into r724 as field;
//     hash.bhp256 r2 into r725 as field;
//     hash.bhp256 r2 into r726 as field;
//     hash.bhp256 r2 into r727 as field;
//     hash.bhp256 r2 into r728 as field;
//     hash.bhp256 r2 into r729 as field;
//     hash.bhp256 r2 into r730 as field;
//     hash.bhp256 r2 into r731 as field;
//     hash.bhp256 r2 into r732 as field;
//     hash.bhp256 r2 into r733 as field;
//     hash.bhp256 r2 into r734 as field;
//     hash.bhp256 r2 into r735 as field;
//     hash.bhp256 r2 into r736 as field;
//     hash.bhp256 r2 into r737 as field;
//     hash.bhp256 r2 into r738 as field;
//     hash.bhp256 r2 into r739 as field;
//     hash.bhp256 r2 into r740 as field;
//     hash.bhp256 r2 into r741 as field;
//     hash.bhp256 r2 into r742 as field;
//     hash.bhp256 r2 into r743 as field;
//     hash.bhp256 r2 into r744 as field;
//     hash.bhp256 r2 into r745 as field;
//     hash.bhp256 r2 into r746 as field;
//     hash.bhp256 r2 into r747 as field;
//     hash.bhp256 r2 into r748 as field;
//     hash.bhp256 r2 into r749 as field;
//     hash.bhp256 r2 into r750 as field;
//     hash.bhp256 r2 into r751 as field;
//     hash.bhp256 r2 into r752 as field;
//     hash.bhp256 r2 into r753 as field;
//     hash.bhp256 r2 into r754 as field;
//     hash.bhp256 r2 into r755 as field;
//     hash.bhp256 r2 into r756 as field;
//     hash.bhp256 r2 into r757 as field;
//     hash.bhp256 r2 into r758 as field;
//     hash.bhp256 r2 into r759 as field;
//     hash.bhp256 r2 into r760 as field;
//     hash.bhp256 r2 into r761 as field;
//     hash.bhp256 r2 into r762 as field;
//     hash.bhp256 r2 into r763 as field;
//     hash.bhp256 r2 into r764 as field;
//     hash.bhp256 r2 into r765 as field;
//     hash.bhp256 r2 into r766 as field;
//     hash.bhp256 r2 into r767 as field;
//     hash.bhp256 r2 into r768 as field;
//     hash.bhp256 r2 into r769 as field;
//     hash.bhp256 r2 into r770 as field;
//     hash.bhp256 r2 into r771 as field;
//     hash.bhp256 r2 into r772 as field;
//     hash.bhp256 r2 into r773 as field;
//     hash.bhp256 r2 into r774 as field;
//     hash.bhp256 r2 into r775 as field;
//     hash.bhp256 r2 into r776 as field;
//     hash.bhp256 r2 into r777 as field;
//     hash.bhp256 r2 into r778 as field;
//     hash.bhp256 r2 into r779 as field;
//     hash.bhp256 r2 into r780 as field;
//     hash.bhp256 r2 into r781 as field;
//     hash.bhp256 r2 into r782 as field;
//     hash.bhp256 r2 into r783 as field;
//     hash.bhp256 r2 into r784 as field;
//     hash.bhp256 r2 into r785 as field;
//     hash.bhp256 r2 into r786 as field;
//     hash.bhp256 r2 into r787 as field;
//     hash.bhp256 r2 into r788 as field;
//     hash.bhp256 r2 into r789 as field;
//     hash.bhp256 r2 into r790 as field;
//     hash.bhp256 r2 into r791 as field;
//     hash.bhp256 r2 into r792 as field;
//     hash.bhp256 r2 into r793 as field;
//     hash.bhp256 r2 into r794 as field;
//     hash.bhp256 r2 into r795 as field;
//     hash.bhp256 r2 into r796 as field;
//     hash.bhp256 r2 into r797 as field;
//     hash.bhp256 r2 into r798 as field;
//     hash.bhp256 r2 into r799 as field;
//     hash.bhp256 r2 into r800 as field;
//     hash.bhp256 r2 into r801 as field;
//     hash.bhp256 r2 into r802 as field;
//     hash.bhp256 r2 into r803 as field;
//     hash.bhp256 r2 into r804 as field;
//     hash.bhp256 r2 into r805 as field;
//     hash.bhp256 r2 into r806 as field;
//     hash.bhp256 r2 into r807 as field;
//     hash.bhp256 r2 into r808 as field;
//     hash.bhp256 r2 into r809 as field;
//     hash.bhp256 r2 into r810 as field;
//     hash.bhp256 r2 into r811 as field;
//     hash.bhp256 r2 into r812 as field;
//     hash.bhp256 r2 into r813 as field;
//     hash.bhp256 r2 into r814 as field;
//     hash.bhp256 r2 into r815 as field;
//     hash.bhp256 r2 into r816 as field;
//     hash.bhp256 r2 into r817 as field;
//     hash.bhp256 r2 into r818 as field;
//     hash.bhp256 r2 into r819 as field;
//     hash.bhp256 r2 into r820 as field;
//     hash.bhp256 r2 into r821 as field;
//     hash.bhp256 r2 into r822 as field;
//     hash.bhp256 r2 into r823 as field;
//     hash.bhp256 r2 into r824 as field;
//     hash.bhp256 r2 into r825 as field;
//     hash.bhp256 r2 into r826 as field;
//     hash.bhp256 r2 into r827 as field;
//     hash.bhp256 r2 into r828 as field;
//     hash.bhp256 r2 into r829 as field;
//     hash.bhp256 r2 into r830 as field;
//     hash.bhp256 r2 into r831 as field;
//     hash.bhp256 r2 into r832 as field;
//     hash.bhp256 r2 into r833 as field;
//     hash.bhp256 r2 into r834 as field;
//     hash.bhp256 r2 into r835 as field;
//     hash.bhp256 r2 into r836 as field;
//     hash.bhp256 r2 into r837 as field;
//     hash.bhp256 r2 into r838 as field;
//     hash.bhp256 r2 into r839 as field;
//     hash.bhp256 r2 into r840 as field;
//     hash.bhp256 r2 into r841 as field;
//     hash.bhp256 r2 into r842 as field;
//     hash.bhp256 r2 into r843 as field;
//     hash.bhp256 r2 into r844 as field;
//     hash.bhp256 r2 into r845 as field;
//     hash.bhp256 r2 into r846 as field;
//     hash.bhp256 r2 into r847 as field;
//     hash.bhp256 r2 into r848 as field;
//     hash.bhp256 r2 into r849 as field;
//     hash.bhp256 r2 into r850 as field;
//     hash.bhp256 r2 into r851 as field;
//     hash.bhp256 r2 into r852 as field;
//     hash.bhp256 r2 into r853 as field;
//     hash.bhp256 r2 into r854 as field;
//     hash.bhp256 r2 into r855 as field;
//     hash.bhp256 r2 into r856 as field;
//     hash.bhp256 r2 into r857 as field;
//     hash.bhp256 r2 into r858 as field;
//     hash.bhp256 r2 into r859 as field;
//     hash.bhp256 r2 into r860 as field;
//     hash.bhp256 r2 into r861 as field;
//     hash.bhp256 r2 into r862 as field;
//     hash.bhp256 r2 into r863 as field;
//     hash.bhp256 r2 into r864 as field;
//     hash.bhp256 r2 into r865 as field;
//     hash.bhp256 r2 into r866 as field;
//     hash.bhp256 r2 into r867 as field;
//     hash.bhp256 r2 into r868 as field;
//     hash.bhp256 r2 into r869 as field;
//     hash.bhp256 r2 into r870 as field;
//     hash.bhp256 r2 into r871 as field;
//     hash.bhp256 r2 into r872 as field;
//     hash.bhp256 r2 into r873 as field;
//     hash.bhp256 r2 into r874 as field;
//     hash.bhp256 r2 into r875 as field;
//     hash.bhp256 r2 into r876 as field;
//     hash.bhp256 r2 into r877 as field;
//     hash.bhp256 r2 into r878 as field;
//     hash.bhp256 r2 into r879 as field;
//     hash.bhp256 r2 into r880 as field;
//     hash.bhp256 r2 into r881 as field;
//     hash.bhp256 r2 into r882 as field;
//     hash.bhp256 r2 into r883 as field;
//     hash.bhp256 r2 into r884 as field;
//     hash.bhp256 r2 into r885 as field;
//     hash.bhp256 r2 into r886 as field;
//     hash.bhp256 r2 into r887 as field;
//     hash.bhp256 r2 into r888 as field;
//     hash.bhp256 r2 into r889 as field;
//     hash.bhp256 r2 into r890 as field;
//     hash.bhp256 r2 into r891 as field;
//     hash.bhp256 r2 into r892 as field;
//     hash.bhp256 r2 into r893 as field;
//     hash.bhp256 r2 into r894 as field;
//     hash.bhp256 r2 into r895 as field;
//     hash.bhp256 r2 into r896 as field;
//     hash.bhp256 r2 into r897 as field;
//     hash.bhp256 r2 into r898 as field;
//     hash.bhp256 r2 into r899 as field;
//     hash.bhp256 r2 into r900 as field;
//     hash.bhp256 r2 into r901 as field;
//     hash.bhp256 r2 into r902 as field;
//     hash.bhp256 r2 into r903 as field;
//     hash.bhp256 r2 into r904 as field;
//     hash.bhp256 r2 into r905 as field;
//     hash.bhp256 r2 into r906 as field;
//     hash.bhp256 r2 into r907 as field;
//     hash.bhp256 r2 into r908 as field;
//     hash.bhp256 r2 into r909 as field;
//     hash.bhp256 r2 into r910 as field;
//     hash.bhp256 r2 into r911 as field;
//     hash.bhp256 r2 into r912 as field;
//     hash.bhp256 r2 into r913 as field;
//     hash.bhp256 r2 into r914 as field;
//     hash.bhp256 r2 into r915 as field;
//     hash.bhp256 r2 into r916 as field;
//     hash.bhp256 r2 into r917 as field;
//     hash.bhp256 r2 into r918 as field;
//     hash.bhp256 r2 into r919 as field;
//     hash.bhp256 r2 into r920 as field;
//     hash.bhp256 r2 into r921 as field;
//     hash.bhp256 r2 into r922 as field;
//     hash.bhp256 r2 into r923 as field;
//     hash.bhp256 r2 into r924 as field;
//     hash.bhp256 r2 into r925 as field;
//     hash.bhp256 r2 into r926 as field;
//     hash.bhp256 r2 into r927 as field;
//     hash.bhp256 r2 into r928 as field;
//     hash.bhp256 r2 into r929 as field;
//     hash.bhp256 r2 into r930 as field;
//     hash.bhp256 r2 into r931 as field;
//     hash.bhp256 r2 into r932 as field;
//     hash.bhp256 r2 into r933 as field;
//     hash.bhp256 r2 into r934 as field;
//     hash.bhp256 r2 into r935 as field;
//     hash.bhp256 r2 into r936 as field;
//     hash.bhp256 r2 into r937 as field;
//     hash.bhp256 r2 into r938 as field;
//     hash.bhp256 r2 into r939 as field;
//     hash.bhp256 r2 into r940 as field;
//     hash.bhp256 r2 into r941 as field;
//     hash.bhp256 r2 into r942 as field;
//     hash.bhp256 r2 into r943 as field;
//     hash.bhp256 r2 into r944 as field;
//     hash.bhp256 r2 into r945 as field;
//     hash.bhp256 r2 into r946 as field;
//     hash.bhp256 r2 into r947 as field;
//     hash.bhp256 r2 into r948 as field;
//     hash.bhp256 r2 into r949 as field;
//     hash.bhp256 r2 into r950 as field;
//     hash.bhp256 r2 into r951 as field;
//     hash.bhp256 r2 into r952 as field;
//     hash.bhp256 r2 into r953 as field;
//     hash.bhp256 r2 into r954 as field;
//     hash.bhp256 r2 into r955 as field;
//     hash.bhp256 r2 into r956 as field;
//     hash.bhp256 r2 into r957 as field;
//     hash.bhp256 r2 into r958 as field;
//     hash.bhp256 r2 into r959 as field;
//     hash.bhp256 r2 into r960 as field;
//     hash.bhp256 r2 into r961 as field;
//     hash.bhp256 r2 into r962 as field;
//     hash.bhp256 r2 into r963 as field;
//     hash.bhp256 r2 into r964 as field;
//     hash.bhp256 r2 into r965 as field;
//     hash.bhp256 r2 into r966 as field;
//     hash.bhp256 r2 into r967 as field;
//     hash.bhp256 r2 into r968 as field;
//     hash.bhp256 r2 into r969 as field;
//     hash.bhp256 r2 into r970 as field;
//     hash.bhp256 r2 into r971 as field;
//     hash.bhp256 r2 into r972 as field;
//     hash.bhp256 r2 into r973 as field;
//     hash.bhp256 r2 into r974 as field;
//     hash.bhp256 r2 into r975 as field;
//     hash.bhp256 r2 into r976 as field;
//     hash.bhp256 r2 into r977 as field;
//     hash.bhp256 r2 into r978 as field;
//     hash.bhp256 r2 into r979 as field;
//     hash.bhp256 r2 into r980 as field;
//     hash.bhp256 r2 into r981 as field;
//     hash.bhp256 r2 into r982 as field;
//     hash.bhp256 r2 into r983 as field;
//     hash.bhp256 r2 into r984 as field;
//     hash.bhp256 r2 into r985 as field;
//     hash.bhp256 r2 into r986 as field;
//     hash.bhp256 r2 into r987 as field;
//     hash.bhp256 r2 into r988 as field;
//     hash.bhp256 r2 into r989 as field;
//     hash.bhp256 r2 into r990 as field;
//     hash.bhp256 r2 into r991 as field;
//     hash.bhp256 r2 into r992 as field;
//     hash.bhp256 r2 into r993 as field;
//     hash.bhp256 r2 into r994 as field;
//     hash.bhp256 r2 into r995 as field;
//     hash.bhp256 r2 into r996 as field;
//     hash.bhp256 r2 into r997 as field;
//     hash.bhp256 r2 into r998 as field;
//     hash.bhp256 r2 into r999 as field;
//     hash.bhp256 r2 into r1000 as field;
//     hash.bhp256 r2 into r1001 as field;
//     hash.bhp256 r2 into r1002 as field;
//     hash.bhp256 r2 into r1003 as field;
//     hash.bhp256 r2 into r1004 as field;
//     hash.bhp256 r2 into r1005 as field;
//     hash.bhp256 r2 into r1006 as field;
//     hash.bhp256 r2 into r1007 as field;
//     hash.bhp256 r2 into r1008 as field;
//     hash.bhp256 r2 into r1009 as field;
//     hash.bhp256 r2 into r1010 as field;
//     hash.bhp256 r2 into r1011 as field;
//     hash.bhp256 r2 into r1012 as field;
//     hash.bhp256 r2 into r1013 as field;
//     hash.bhp256 r2 into r1014 as field;
//     hash.bhp256 r2 into r1015 as field;
//     hash.bhp256 r2 into r1016 as field;
//     hash.bhp256 r2 into r1017 as field;
//     hash.bhp256 r2 into r1018 as field;
//     hash.bhp256 r2 into r1019 as field;
//     hash.bhp256 r2 into r1020 as field;
//     hash.bhp256 r2 into r1021 as field;
//     hash.bhp256 r2 into r1022 as field;
//     hash.bhp256 r2 into r1023 as field;
//     hash.bhp256 r2 into r1024 as field;
//     hash.bhp256 r2 into r1025 as field;
//     hash.bhp256 r2 into r1026 as field;
//     hash.bhp256 r2 into r1027 as field;
//     hash.bhp256 r2 into r1028 as field;
//     hash.bhp256 r2 into r1029 as field;
//     hash.bhp256 r2 into r1030 as field;
//     hash.bhp256 r2 into r1031 as field;
//     hash.bhp256 r2 into r1032 as field;
//     hash.bhp256 r2 into r1033 as field;
//     hash.bhp256 r2 into r1034 as field;
//     hash.bhp256 r2 into r1035 as field;
//     hash.bhp256 r2 into r1036 as field;
//     hash.bhp256 r2 into r1037 as field;
//     hash.bhp256 r2 into r1038 as field;
//     hash.bhp256 r2 into r1039 as field;
//     hash.bhp256 r2 into r1040 as field;
//     hash.bhp256 r2 into r1041 as field;
//     hash.bhp256 r2 into r1042 as field;
//     hash.bhp256 r2 into r1043 as field;
//     hash.bhp256 r2 into r1044 as field;
//     hash.bhp256 r2 into r1045 as field;
//     hash.bhp256 r2 into r1046 as field;
//     hash.bhp256 r2 into r1047 as field;
//     hash.bhp256 r2 into r1048 as field;
//     hash.bhp256 r2 into r1049 as field;
//     hash.bhp256 r2 into r1050 as field;
//     hash.bhp256 r2 into r1051 as field;
//     hash.bhp256 r2 into r1052 as field;
//     hash.bhp256 r2 into r1053 as field;
//     hash.bhp256 r2 into r1054 as field;
//     hash.bhp256 r2 into r1055 as field;
//     hash.bhp256 r2 into r1056 as field;
//     hash.bhp256 r2 into r1057 as field;
//     hash.bhp256 r2 into r1058 as field;
//     hash.bhp256 r2 into r1059 as field;
//     hash.bhp256 r2 into r1060 as field;
//     hash.bhp256 r2 into r1061 as field;
//     hash.bhp256 r2 into r1062 as field;
//     hash.bhp256 r2 into r1063 as field;
//     hash.bhp256 r2 into r1064 as field;
//     hash.bhp256 r2 into r1065 as field;
//     hash.bhp256 r2 into r1066 as field;
//     hash.bhp256 r2 into r1067 as field;
//     hash.bhp256 r2 into r1068 as field;
//     hash.bhp256 r2 into r1069 as field;
//     hash.bhp256 r2 into r1070 as field;
//     hash.bhp256 r2 into r1071 as field;
//     hash.bhp256 r2 into r1072 as field;
//     hash.bhp256 r2 into r1073 as field;
//     hash.bhp256 r2 into r1074 as field;
//     hash.bhp256 r2 into r1075 as field;
//     hash.bhp256 r2 into r1076 as field;
//     hash.bhp256 r2 into r1077 as field;
//     hash.bhp256 r2 into r1078 as field;
//     hash.bhp256 r2 into r1079 as field;
//     hash.bhp256 r2 into r1080 as field;
//     hash.bhp256 r2 into r1081 as field;
//     hash.bhp256 r2 into r1082 as field;
//     hash.bhp256 r2 into r1083 as field;
//     hash.bhp256 r2 into r1084 as field;
//     hash.bhp256 r2 into r1085 as field;
//     hash.bhp256 r2 into r1086 as field;
//     hash.bhp256 r2 into r1087 as field;
//     hash.bhp256 r2 into r1088 as field;
//     hash.bhp256 r2 into r1089 as field;
//     hash.bhp256 r2 into r1090 as field;
//     hash.bhp256 r2 into r1091 as field;
//     hash.bhp256 r2 into r1092 as field;
//     hash.bhp256 r2 into r1093 as field;
//     hash.bhp256 r2 into r1094 as field;
//     hash.bhp256 r2 into r1095 as field;
//     hash.bhp256 r2 into r1096 as field;
//     hash.bhp256 r2 into r1097 as field;
//     hash.bhp256 r2 into r1098 as field;
//     hash.bhp256 r2 into r1099 as field;
//     hash.bhp256 r2 into r1100 as field;
//     hash.bhp256 r2 into r1101 as field;
//     hash.bhp256 r2 into r1102 as field;
//     hash.bhp256 r2 into r1103 as field;
//     hash.bhp256 r2 into r1104 as field;
//     hash.bhp256 r2 into r1105 as field;
//     hash.bhp256 r2 into r1106 as field;
//     hash.bhp256 r2 into r1107 as field;
//     hash.bhp256 r2 into r1108 as field;
//     hash.bhp256 r2 into r1109 as field;
//     hash.bhp256 r2 into r1110 as field;
//     hash.bhp256 r2 into r1111 as field;
//     hash.bhp256 r2 into r1112 as field;
//     hash.bhp256 r2 into r1113 as field;
//     hash.bhp256 r2 into r1114 as field;
//     hash.bhp256 r2 into r1115 as field;
//     hash.bhp256 r2 into r1116 as field;
//     hash.bhp256 r2 into r1117 as field;
//     hash.bhp256 r2 into r1118 as field;
//     hash.bhp256 r2 into r1119 as field;
//     hash.bhp256 r2 into r1120 as field;
//     hash.bhp256 r2 into r1121 as field;
//     hash.bhp256 r2 into r1122 as field;
//     hash.bhp256 r2 into r1123 as field;
//     hash.bhp256 r2 into r1124 as field;
//     hash.bhp256 r2 into r1125 as field;
//     hash.bhp256 r2 into r1126 as field;
//     hash.bhp256 r2 into r1127 as field;
//     hash.bhp256 r2 into r1128 as field;
//     hash.bhp256 r2 into r1129 as field;
//     hash.bhp256 r2 into r1130 as field;
//     hash.bhp256 r2 into r1131 as field;
//     hash.bhp256 r2 into r1132 as field;
//     hash.bhp256 r2 into r1133 as field;
//     hash.bhp256 r2 into r1134 as field;
//     hash.bhp256 r2 into r1135 as field;
//     hash.bhp256 r2 into r1136 as field;
//     hash.bhp256 r2 into r1137 as field;
//     hash.bhp256 r2 into r1138 as field;
//     hash.bhp256 r2 into r1139 as field;
//     hash.bhp256 r2 into r1140 as field;
//     hash.bhp256 r2 into r1141 as field;
//     hash.bhp256 r2 into r1142 as field;
//     hash.bhp256 r2 into r1143 as field;
//     hash.bhp256 r2 into r1144 as field;
//     hash.bhp256 r2 into r1145 as field;
//     hash.bhp256 r2 into r1146 as field;
//     hash.bhp256 r2 into r1147 as field;
//     hash.bhp256 r2 into r1148 as field;
//     hash.bhp256 r2 into r1149 as field;
//     hash.bhp256 r2 into r1150 as field;
//     hash.bhp256 r2 into r1151 as field;
//     hash.bhp256 r2 into r1152 as field;
//     hash.bhp256 r2 into r1153 as field;
//     hash.bhp256 r2 into r1154 as field;
//     hash.bhp256 r2 into r1155 as field;
//     hash.bhp256 r2 into r1156 as field;
//     hash.bhp256 r2 into r1157 as field;
//     hash.bhp256 r2 into r1158 as field;
//     hash.bhp256 r2 into r1159 as field;
//     hash.bhp256 r2 into r1160 as field;
//     hash.bhp256 r2 into r1161 as field;
//     hash.bhp256 r2 into r1162 as field;
//     hash.bhp256 r2 into r1163 as field;
//     hash.bhp256 r2 into r1164 as field;
//     hash.bhp256 r2 into r1165 as field;
//     hash.bhp256 r2 into r1166 as field;
//     hash.bhp256 r2 into r1167 as field;
//     hash.bhp256 r2 into r1168 as field;
//     hash.bhp256 r2 into r1169 as field;
//     hash.bhp256 r2 into r1170 as field;
//     hash.bhp256 r2 into r1171 as field;
//     hash.bhp256 r2 into r1172 as field;
//     hash.bhp256 r2 into r1173 as field;
//     hash.bhp256 r2 into r1174 as field;
//     hash.bhp256 r2 into r1175 as field;
//     hash.bhp256 r2 into r1176 as field;
//     hash.bhp256 r2 into r1177 as field;
//     hash.bhp256 r2 into r1178 as field;
//     hash.bhp256 r2 into r1179 as field;
//     hash.bhp256 r2 into r1180 as field;
//     hash.bhp256 r2 into r1181 as field;
//     hash.bhp256 r2 into r1182 as field;
//     hash.bhp256 r2 into r1183 as field;
//     hash.bhp256 r2 into r1184 as field;
//     hash.bhp256 r2 into r1185 as field;
//     hash.bhp256 r2 into r1186 as field;
//     hash.bhp256 r2 into r1187 as field;
//     hash.bhp256 r2 into r1188 as field;
//     hash.bhp256 r2 into r1189 as field;
//     hash.bhp256 r2 into r1190 as field;
//     hash.bhp256 r2 into r1191 as field;
//     hash.bhp256 r2 into r1192 as field;
//     hash.bhp256 r2 into r1193 as field;
//     hash.bhp256 r2 into r1194 as field;
//     hash.bhp256 r2 into r1195 as field;
//     hash.bhp256 r2 into r1196 as field;
//     hash.bhp256 r2 into r1197 as field;
//     hash.bhp256 r2 into r1198 as field;
//     hash.bhp256 r2 into r1199 as field;
//     hash.bhp256 r2 into r1200 as field;
//     hash.bhp256 r2 into r1201 as field;
//     hash.bhp256 r2 into r1202 as field;
//     hash.bhp256 r2 into r1203 as field;
//     hash.bhp256 r2 into r1204 as field;
//     hash.bhp256 r2 into r1205 as field;
//     hash.bhp256 r2 into r1206 as field;
//     hash.bhp256 r2 into r1207 as field;
//     hash.bhp256 r2 into r1208 as field;
//     hash.bhp256 r2 into r1209 as field;
//     hash.bhp256 r2 into r1210 as field;
//     hash.bhp256 r2 into r1211 as field;
//     hash.bhp256 r2 into r1212 as field;
//     hash.bhp256 r2 into r1213 as field;
//     hash.bhp256 r2 into r1214 as field;
//     hash.bhp256 r2 into r1215 as field;
//     hash.bhp256 r2 into r1216 as field;
//     hash.bhp256 r2 into r1217 as field;
//     hash.bhp256 r2 into r1218 as field;
//     hash.bhp256 r2 into r1219 as field;
//     hash.bhp256 r2 into r1220 as field;
//     hash.bhp256 r2 into r1221 as field;
//     hash.bhp256 r2 into r1222 as field;
//     hash.bhp256 r2 into r1223 as field;
//     hash.bhp256 r2 into r1224 as field;
//     hash.bhp256 r2 into r1225 as field;
//     hash.bhp256 r2 into r1226 as field;
//     hash.bhp256 r2 into r1227 as field;
//     hash.bhp256 r2 into r1228 as field;
//     hash.bhp256 r2 into r1229 as field;
//     hash.bhp256 r2 into r1230 as field;
//     hash.bhp256 r2 into r1231 as field;
//     hash.bhp256 r2 into r1232 as field;
//     hash.bhp256 r2 into r1233 as field;
//     hash.bhp256 r2 into r1234 as field;
//     hash.bhp256 r2 into r1235 as field;
//     hash.bhp256 r2 into r1236 as field;
//     hash.bhp256 r2 into r1237 as field;
//     hash.bhp256 r2 into r1238 as field;
//     hash.bhp256 r2 into r1239 as field;
//     hash.bhp256 r2 into r1240 as field;
//     hash.bhp256 r2 into r1241 as field;
//     hash.bhp256 r2 into r1242 as field;
//     hash.bhp256 r2 into r1243 as field;
//     hash.bhp256 r2 into r1244 as field;
//     hash.bhp256 r2 into r1245 as field;
//     hash.bhp256 r2 into r1246 as field;
//     hash.bhp256 r2 into r1247 as field;
//     hash.bhp256 r2 into r1248 as field;
//     hash.bhp256 r2 into r1249 as field;
//     hash.bhp256 r2 into r1250 as field;
//     hash.bhp256 r2 into r1251 as field;
//     hash.bhp256 r2 into r1252 as field;
//     hash.bhp256 r2 into r1253 as field;
//     hash.bhp256 r2 into r1254 as field;
//     hash.bhp256 r2 into r1255 as field;
//     hash.bhp256 r2 into r1256 as field;
//     hash.bhp256 r2 into r1257 as field;
//     hash.bhp256 r2 into r1258 as field;
//     hash.bhp256 r2 into r1259 as field;
//     hash.bhp256 r2 into r1260 as field;
//     hash.bhp256 r2 into r1261 as field;
//     hash.bhp256 r2 into r1262 as field;
//     hash.bhp256 r2 into r1263 as field;
//     hash.bhp256 r2 into r1264 as field;
//     hash.bhp256 r2 into r1265 as field;
//     hash.bhp256 r2 into r1266 as field;
//     hash.bhp256 r2 into r1267 as field;
//     hash.bhp256 r2 into r1268 as field;
//     hash.bhp256 r2 into r1269 as field;
//     hash.bhp256 r2 into r1270 as field;
//     hash.bhp256 r2 into r1271 as field;
//     hash.bhp256 r2 into r1272 as field;
//     hash.bhp256 r2 into r1273 as field;
//     hash.bhp256 r2 into r1274 as field;
//     hash.bhp256 r2 into r1275 as field;
//     hash.bhp256 r2 into r1276 as field;
//     hash.bhp256 r2 into r1277 as field;
//     hash.bhp256 r2 into r1278 as field;
//     hash.bhp256 r2 into r1279 as field;
//     hash.bhp256 r2 into r1280 as field;
//     hash.bhp256 r2 into r1281 as field;
//     hash.bhp256 r2 into r1282 as field;
//     hash.bhp256 r2 into r1283 as field;
//     hash.bhp256 r2 into r1284 as field;
//     hash.bhp256 r2 into r1285 as field;
//     hash.bhp256 r2 into r1286 as field;
//     hash.bhp256 r2 into r1287 as field;
//     hash.bhp256 r2 into r1288 as field;
//     hash.bhp256 r2 into r1289 as field;
//     hash.bhp256 r2 into r1290 as field;
//     hash.bhp256 r2 into r1291 as field;
//     hash.bhp256 r2 into r1292 as field;
//     hash.bhp256 r2 into r1293 as field;
//     hash.bhp256 r2 into r1294 as field;
//     hash.bhp256 r2 into r1295 as field;
//     hash.bhp256 r2 into r1296 as field;
//     hash.bhp256 r2 into r1297 as field;
//     hash.bhp256 r2 into r1298 as field;
//     hash.bhp256 r2 into r1299 as field;
//     hash.bhp256 r2 into r1300 as field;
//     hash.bhp256 r2 into r1301 as field;
//     hash.bhp256 r2 into r1302 as field;
//     hash.bhp256 r2 into r1303 as field;
//     hash.bhp256 r2 into r1304 as field;
//     hash.bhp256 r2 into r1305 as field;
//     hash.bhp256 r2 into r1306 as field;
//     hash.bhp256 r2 into r1307 as field;
//     hash.bhp256 r2 into r1308 as field;
//     hash.bhp256 r2 into r1309 as field;
//     hash.bhp256 r2 into r1310 as field;
//     hash.bhp256 r2 into r1311 as field;
//     hash.bhp256 r2 into r1312 as field;
//     hash.bhp256 r2 into r1313 as field;
//     hash.bhp256 r2 into r1314 as field;
//     hash.bhp256 r2 into r1315 as field;
//     hash.bhp256 r2 into r1316 as field;
//     hash.bhp256 r2 into r1317 as field;
//     hash.bhp256 r2 into r1318 as field;
//     hash.bhp256 r2 into r1319 as field;
//     hash.bhp256 r2 into r1320 as field;
//     hash.bhp256 r2 into r1321 as field;
//     hash.bhp256 r2 into r1322 as field;
//     hash.bhp256 r2 into r1323 as field;
//     hash.bhp256 r2 into r1324 as field;
//     hash.bhp256 r2 into r1325 as field;
//     hash.bhp256 r2 into r1326 as field;
//     hash.bhp256 r2 into r1327 as field;
//     hash.bhp256 r2 into r1328 as field;
//     hash.bhp256 r2 into r1329 as field;
//     hash.bhp256 r2 into r1330 as field;
//     hash.bhp256 r2 into r1331 as field;
//     hash.bhp256 r2 into r1332 as field;
//     hash.bhp256 r2 into r1333 as field;
//     hash.bhp256 r2 into r1334 as field;
//     hash.bhp256 r2 into r1335 as field;
//     hash.bhp256 r2 into r1336 as field;
//     hash.bhp256 r2 into r1337 as field;
//     hash.bhp256 r2 into r1338 as field;
//     hash.bhp256 r2 into r1339 as field;
//     hash.bhp256 r2 into r1340 as field;
//     hash.bhp256 r2 into r1341 as field;
//     hash.bhp256 r2 into r1342 as field;
//     hash.bhp256 r2 into r1343 as field;
//     hash.bhp256 r2 into r1344 as field;
//     hash.bhp256 r2 into r1345 as field;
//     hash.bhp256 r2 into r1346 as field;
//     hash.bhp256 r2 into r1347 as field;
//     hash.bhp256 r2 into r1348 as field;
//     hash.bhp256 r2 into r1349 as field;
//     hash.bhp256 r2 into r1350 as field;
//     hash.bhp256 r2 into r1351 as field;
//     hash.bhp256 r2 into r1352 as field;
//     hash.bhp256 r2 into r1353 as field;
//     hash.bhp256 r2 into r1354 as field;
//     hash.bhp256 r2 into r1355 as field;
//     hash.bhp256 r2 into r1356 as field;
//     hash.bhp256 r2 into r1357 as field;
//     hash.bhp256 r2 into r1358 as field;
//     hash.bhp256 r2 into r1359 as field;
//     hash.bhp256 r2 into r1360 as field;
//     hash.bhp256 r2 into r1361 as field;
//     hash.bhp256 r2 into r1362 as field;
//     hash.bhp256 r2 into r1363 as field;
//     hash.bhp256 r2 into r1364 as field;
//     hash.bhp256 r2 into r1365 as field;
//     hash.bhp256 r2 into r1366 as field;
//     hash.bhp256 r2 into r1367 as field;
//     hash.bhp256 r2 into r1368 as field;
//     hash.bhp256 r2 into r1369 as field;
//     hash.bhp256 r2 into r1370 as field;
//     hash.bhp256 r2 into r1371 as field;
//     hash.bhp256 r2 into r1372 as field;
//     hash.bhp256 r2 into r1373 as field;
//     hash.bhp256 r2 into r1374 as field;
//     hash.bhp256 r2 into r1375 as field;
//     hash.bhp256 r2 into r1376 as field;
//     hash.bhp256 r2 into r1377 as field;
//     hash.bhp256 r2 into r1378 as field;
//     hash.bhp256 r2 into r1379 as field;
//     hash.bhp256 r2 into r1380 as field;
//     hash.bhp256 r2 into r1381 as field;
//     hash.bhp256 r2 into r1382 as field;
//     hash.bhp256 r2 into r1383 as field;
//     hash.bhp256 r2 into r1384 as field;
//     hash.bhp256 r2 into r1385 as field;
//     hash.bhp256 r2 into r1386 as field;
//     hash.bhp256 r2 into r1387 as field;
//     hash.bhp256 r2 into r1388 as field;
//     hash.bhp256 r2 into r1389 as field;
//     hash.bhp256 r2 into r1390 as field;
//     hash.bhp256 r2 into r1391 as field;
//     hash.bhp256 r2 into r1392 as field;
//     hash.bhp256 r2 into r1393 as field;
//     hash.bhp256 r2 into r1394 as field;
//     hash.bhp256 r2 into r1395 as field;
//     hash.bhp256 r2 into r1396 as field;
//     hash.bhp256 r2 into r1397 as field;
//     hash.bhp256 r2 into r1398 as field;
//     hash.bhp256 r2 into r1399 as field;
//     hash.bhp256 r2 into r1400 as field;
//     hash.bhp256 r2 into r1401 as field;
//     hash.bhp256 r2 into r1402 as field;
//     hash.bhp256 r2 into r1403 as field;
//     hash.bhp256 r2 into r1404 as field;
//     hash.bhp256 r2 into r1405 as field;
//     hash.bhp256 r2 into r1406 as field;
//     hash.bhp256 r2 into r1407 as field;
//     hash.bhp256 r2 into r1408 as field;
//     hash.bhp256 r2 into r1409 as field;
//     hash.bhp256 r2 into r1410 as field;
//     hash.bhp256 r2 into r1411 as field;
//     hash.bhp256 r2 into r1412 as field;
//     hash.bhp256 r2 into r1413 as field;
//     hash.bhp256 r2 into r1414 as field;
//     hash.bhp256 r2 into r1415 as field;
//     hash.bhp256 r2 into r1416 as field;
//     hash.bhp256 r2 into r1417 as field;
//     hash.bhp256 r2 into r1418 as field;
//     hash.bhp256 r2 into r1419 as field;
//     hash.bhp256 r2 into r1420 as field;
//     hash.bhp256 r2 into r1421 as field;
//     hash.bhp256 r2 into r1422 as field;
//     hash.bhp256 r2 into r1423 as field;
//     hash.bhp256 r2 into r1424 as field;
//     hash.bhp256 r2 into r1425 as field;
//     hash.bhp256 r2 into r1426 as field;
//     hash.bhp256 r2 into r1427 as field;
//     hash.bhp256 r2 into r1428 as field;
//     hash.bhp256 r2 into r1429 as field;
//     hash.bhp256 r2 into r1430 as field;
//     hash.bhp256 r2 into r1431 as field;
//     hash.bhp256 r2 into r1432 as field;
//     hash.bhp256 r2 into r1433 as field;
//     hash.bhp256 r2 into r1434 as field;
//     hash.bhp256 r2 into r1435 as field;
//     hash.bhp256 r2 into r1436 as field;
//     hash.bhp256 r2 into r1437 as field;
//     hash.bhp256 r2 into r1438 as field;
//     hash.bhp256 r2 into r1439 as field;
//     hash.bhp256 r2 into r1440 as field;
//     hash.bhp256 r2 into r1441 as field;
//     hash.bhp256 r2 into r1442 as field;
//     hash.bhp256 r2 into r1443 as field;
//     hash.bhp256 r2 into r1444 as field;
//     hash.bhp256 r2 into r1445 as field;
//     hash.bhp256 r2 into r1446 as field;
//     hash.bhp256 r2 into r1447 as field;
//     hash.bhp256 r2 into r1448 as field;
//     hash.bhp256 r2 into r1449 as field;
//     hash.bhp256 r2 into r1450 as field;
//     hash.bhp256 r2 into r1451 as field;
//     hash.bhp256 r2 into r1452 as field;
//     hash.bhp256 r2 into r1453 as field;
//     hash.bhp256 r2 into r1454 as field;
//     hash.bhp256 r2 into r1455 as field;
//     hash.bhp256 r2 into r1456 as field;
//     hash.bhp256 r2 into r1457 as field;
//     hash.bhp256 r2 into r1458 as field;
//     hash.bhp256 r2 into r1459 as field;
//     hash.bhp256 r2 into r1460 as field;
//     hash.bhp256 r2 into r1461 as field;
//     hash.bhp256 r2 into r1462 as field;
//     hash.bhp256 r2 into r1463 as field;
//     hash.bhp256 r2 into r1464 as field;
//     hash.bhp256 r2 into r1465 as field;
//     hash.bhp256 r2 into r1466 as field;
//     hash.bhp256 r2 into r1467 as field;
//     hash.bhp256 r2 into r1468 as field;
//     hash.bhp256 r2 into r1469 as field;
//     hash.bhp256 r2 into r1470 as field;
//     hash.bhp256 r2 into r1471 as field;
//     hash.bhp256 r2 into r1472 as field;
//     hash.bhp256 r2 into r1473 as field;
//     hash.bhp256 r2 into r1474 as field;
//     hash.bhp256 r2 into r1475 as field;
//     hash.bhp256 r2 into r1476 as field;
//     hash.bhp256 r2 into r1477 as field;
//     hash.bhp256 r2 into r1478 as field;
//     hash.bhp256 r2 into r1479 as field;
//     hash.bhp256 r2 into r1480 as field;
//     hash.bhp256 r2 into r1481 as field;
//     hash.bhp256 r2 into r1482 as field;
//     hash.bhp256 r2 into r1483 as field;
//     hash.bhp256 r2 into r1484 as field;
//     hash.bhp256 r2 into r1485 as field;
//     hash.bhp256 r2 into r1486 as field;
//     hash.bhp256 r2 into r1487 as field;
//     hash.bhp256 r2 into r1488 as field;
//     hash.bhp256 r2 into r1489 as field;
//     hash.bhp256 r2 into r1490 as field;
//     hash.bhp256 r2 into r1491 as field;
//     hash.bhp256 r2 into r1492 as field;
//     hash.bhp256 r2 into r1493 as field;
//     hash.bhp256 r2 into r1494 as field;
//     hash.bhp256 r2 into r1495 as field;
//     hash.bhp256 r2 into r1496 as field;
//     hash.bhp256 r2 into r1497 as field;
//     hash.bhp256 r2 into r1498 as field;
//     hash.bhp256 r2 into r1499 as field;
//     hash.bhp256 r2 into r1500 as field;
//     hash.bhp256 r2 into r1501 as field;
//     hash.bhp256 r2 into r1502 as field;
//     hash.bhp256 r2 into r1503 as field;
//     hash.bhp256 r2 into r1504 as field;
//     hash.bhp256 r2 into r1505 as field;
//     hash.bhp256 r2 into r1506 as field;
//     hash.bhp256 r2 into r1507 as field;
//     hash.bhp256 r2 into r1508 as field;
//     hash.bhp256 r2 into r1509 as field;
//     hash.bhp256 r2 into r1510 as field;
//     hash.bhp256 r2 into r1511 as field;
//     hash.bhp256 r2 into r1512 as field;
//     hash.bhp256 r2 into r1513 as field;
//     hash.bhp256 r2 into r1514 as field;
//     hash.bhp256 r2 into r1515 as field;
//     hash.bhp256 r2 into r1516 as field;
//     hash.bhp256 r2 into r1517 as field;
//     hash.bhp256 r2 into r1518 as field;
//     hash.bhp256 r2 into r1519 as field;
//     hash.bhp256 r2 into r1520 as field;
//     hash.bhp256 r2 into r1521 as field;
//     hash.bhp256 r2 into r1522 as field;
//     hash.bhp256 r2 into r1523 as field;
//     hash.bhp256 r2 into r1524 as field;
//     hash.bhp256 r2 into r1525 as field;
//     hash.bhp256 r2 into r1526 as field;
//     hash.bhp256 r2 into r1527 as field;
//     hash.bhp256 r2 into r1528 as field;
//     hash.bhp256 r2 into r1529 as field;
//     hash.bhp256 r2 into r1530 as field;
//     hash.bhp256 r2 into r1531 as field;
//     hash.bhp256 r2 into r1532 as field;
//     hash.bhp256 r2 into r1533 as field;
//     hash.bhp256 r2 into r1534 as field;
//     hash.bhp256 r2 into r1535 as field;
//     hash.bhp256 r2 into r1536 as field;
//     hash.bhp256 r2 into r1537 as field;
//     hash.bhp256 r2 into r1538 as field;
//     hash.bhp256 r2 into r1539 as field;
//     hash.bhp256 r2 into r1540 as field;
//     hash.bhp256 r2 into r1541 as field;
//     hash.bhp256 r2 into r1542 as field;
//     hash.bhp256 r2 into r1543 as field;
//     hash.bhp256 r2 into r1544 as field;
//     hash.bhp256 r2 into r1545 as field;
//     hash.bhp256 r2 into r1546 as field;
//     hash.bhp256 r2 into r1547 as field;
//     hash.bhp256 r2 into r1548 as field;
//     hash.bhp256 r2 into r1549 as field;
//     hash.bhp256 r2 into r1550 as field;
//     hash.bhp256 r2 into r1551 as field;
//     hash.bhp256 r2 into r1552 as field;
//     hash.bhp256 r2 into r1553 as field;
//     hash.bhp256 r2 into r1554 as field;
//     hash.bhp256 r2 into r1555 as field;
//     hash.bhp256 r2 into r1556 as field;
//     hash.bhp256 r2 into r1557 as field;
//     hash.bhp256 r2 into r1558 as field;
//     hash.bhp256 r2 into r1559 as field;
//     hash.bhp256 r2 into r1560 as field;
//     hash.bhp256 r2 into r1561 as field;
//     hash.bhp256 r2 into r1562 as field;
//     hash.bhp256 r2 into r1563 as field;
//     hash.bhp256 r2 into r1564 as field;
//     hash.bhp256 r2 into r1565 as field;
//     hash.bhp256 r2 into r1566 as field;
//     hash.bhp256 r2 into r1567 as field;
//     hash.bhp256 r2 into r1568 as field;
//     hash.bhp256 r2 into r1569 as field;
//     hash.bhp256 r2 into r1570 as field;
//     hash.bhp256 r2 into r1571 as field;
//     hash.bhp256 r2 into r1572 as field;
//     hash.bhp256 r2 into r1573 as field;
//     hash.bhp256 r2 into r1574 as field;
//     hash.bhp256 r2 into r1575 as field;
//     hash.bhp256 r2 into r1576 as field;
//     hash.bhp256 r2 into r1577 as field;
//     hash.bhp256 r2 into r1578 as field;
//     hash.bhp256 r2 into r1579 as field;
//     hash.bhp256 r2 into r1580 as field;
//     hash.bhp256 r2 into r1581 as field;
//     hash.bhp256 r2 into r1582 as field;
//     hash.bhp256 r2 into r1583 as field;
//     hash.bhp256 r2 into r1584 as field;
//     hash.bhp256 r2 into r1585 as field;
//     hash.bhp256 r2 into r1586 as field;
//     hash.bhp256 r2 into r1587 as field;
//     hash.bhp256 r2 into r1588 as field;
//     hash.bhp256 r2 into r1589 as field;
//     hash.bhp256 r2 into r1590 as field;
//     hash.bhp256 r2 into r1591 as field;
//     hash.bhp256 r2 into r1592 as field;
//     hash.bhp256 r2 into r1593 as field;
//     hash.bhp256 r2 into r1594 as field;
//     hash.bhp256 r2 into r1595 as field;
//     hash.bhp256 r2 into r1596 as field;
//     hash.bhp256 r2 into r1597 as field;
//     hash.bhp256 r2 into r1598 as field;
//     hash.bhp256 r2 into r1599 as field;
//     hash.bhp256 r2 into r1600 as field;
//     hash.bhp256 r2 into r1601 as field;
//     hash.bhp256 r2 into r1602 as field;
//     hash.bhp256 r2 into r1603 as field;
//     hash.bhp256 r2 into r1604 as field;
//     hash.bhp256 r2 into r1605 as field;
//     hash.bhp256 r2 into r1606 as field;
//     hash.bhp256 r2 into r1607 as field;
//     hash.bhp256 r2 into r1608 as field;
//     hash.bhp256 r2 into r1609 as field;
//     hash.bhp256 r2 into r1610 as field;
//     hash.bhp256 r2 into r1611 as field;
//     hash.bhp256 r2 into r1612 as field;
//     hash.bhp256 r2 into r1613 as field;
//     hash.bhp256 r2 into r1614 as field;
//     hash.bhp256 r2 into r1615 as field;
//     hash.bhp256 r2 into r1616 as field;
//     hash.bhp256 r2 into r1617 as field;
//     hash.bhp256 r2 into r1618 as field;
//     hash.bhp256 r2 into r1619 as field;
//     hash.bhp256 r2 into r1620 as field;
//     hash.bhp256 r2 into r1621 as field;
//     hash.bhp256 r2 into r1622 as field;
//     hash.bhp256 r2 into r1623 as field;
//     hash.bhp256 r2 into r1624 as field;
//     hash.bhp256 r2 into r1625 as field;
//     hash.bhp256 r2 into r1626 as field;
//     hash.bhp256 r2 into r1627 as field;
//     hash.bhp256 r2 into r1628 as field;
//     hash.bhp256 r2 into r1629 as field;
//     hash.bhp256 r2 into r1630 as field;
//     hash.bhp256 r2 into r1631 as field;
//     hash.bhp256 r2 into r1632 as field;
//     hash.bhp256 r2 into r1633 as field;
//     hash.bhp256 r2 into r1634 as field;
//     hash.bhp256 r2 into r1635 as field;
//     hash.bhp256 r2 into r1636 as field;
//     hash.bhp256 r2 into r1637 as field;
//     hash.bhp256 r2 into r1638 as field;
//     hash.bhp256 r2 into r1639 as field;
//     hash.bhp256 r2 into r1640 as field;
//     hash.bhp256 r2 into r1641 as field;
//     hash.bhp256 r2 into r1642 as field;
//     hash.bhp256 r2 into r1643 as field;
//     hash.bhp256 r2 into r1644 as field;
//     hash.bhp256 r2 into r1645 as field;
//     hash.bhp256 r2 into r1646 as field;
//     hash.bhp256 r2 into r1647 as field;
//     hash.bhp256 r2 into r1648 as field;
//     hash.bhp256 r2 into r1649 as field;
//     hash.bhp256 r2 into r1650 as field;
//     hash.bhp256 r2 into r1651 as field;
//     hash.bhp256 r2 into r1652 as field;
//     hash.bhp256 r2 into r1653 as field;
//     hash.bhp256 r2 into r1654 as field;
//     hash.bhp256 r2 into r1655 as field;
//     hash.bhp256 r2 into r1656 as field;
//     hash.bhp256 r2 into r1657 as field;
//     hash.bhp256 r2 into r1658 as field;
//     hash.bhp256 r2 into r1659 as field;
//     hash.bhp256 r2 into r1660 as field;
//     hash.bhp256 r2 into r1661 as field;
//     hash.bhp256 r2 into r1662 as field;
//     hash.bhp256 r2 into r1663 as field;
//     hash.bhp256 r2 into r1664 as field;
//     hash.bhp256 r2 into r1665 as field;
//     hash.bhp256 r2 into r1666 as field;
//     hash.bhp256 r2 into r1667 as field;
//     hash.bhp256 r2 into r1668 as field;
//     hash.bhp256 r2 into r1669 as field;
//     hash.bhp256 r2 into r1670 as field;
//     hash.bhp256 r2 into r1671 as field;
//     hash.bhp256 r2 into r1672 as field;
//     hash.bhp256 r2 into r1673 as field;
//     hash.bhp256 r2 into r1674 as field;
//     hash.bhp256 r2 into r1675 as field;
//     hash.bhp256 r2 into r1676 as field;
//     hash.bhp256 r2 into r1677 as field;
//     hash.bhp256 r2 into r1678 as field;
//     hash.bhp256 r2 into r1679 as field;
//     hash.bhp256 r2 into r1680 as field;
//     hash.bhp256 r2 into r1681 as field;
//     hash.bhp256 r2 into r1682 as field;
//     hash.bhp256 r2 into r1683 as field;
//     hash.bhp256 r2 into r1684 as field;
//     hash.bhp256 r2 into r1685 as field;
//     hash.bhp256 r2 into r1686 as field;
//     hash.bhp256 r2 into r1687 as field;
//     hash.bhp256 r2 into r1688 as field;
//     hash.bhp256 r2 into r1689 as field;
//     hash.bhp256 r2 into r1690 as field;
//     hash.bhp256 r2 into r1691 as field;
//     hash.bhp256 r2 into r1692 as field;
//     hash.bhp256 r2 into r1693 as field;
//     hash.bhp256 r2 into r1694 as field;
//     hash.bhp256 r2 into r1695 as field;
//     hash.bhp256 r2 into r1696 as field;
//     hash.bhp256 r2 into r1697 as field;
//     hash.bhp256 r2 into r1698 as field;
//     hash.bhp256 r2 into r1699 as field;
//     hash.bhp256 r2 into r1700 as field;
//     hash.bhp256 r2 into r1701 as field;
//     hash.bhp256 r2 into r1702 as field;
//     hash.bhp256 r2 into r1703 as field;
//     hash.bhp256 r2 into r1704 as field;
//     hash.bhp256 r2 into r1705 as field;
//     hash.bhp256 r2 into r1706 as field;
//     hash.bhp256 r2 into r1707 as field;
//     hash.bhp256 r2 into r1708 as field;
//     hash.bhp256 r2 into r1709 as field;
//     hash.bhp256 r2 into r1710 as field;
//     hash.bhp256 r2 into r1711 as field;
//     hash.bhp256 r2 into r1712 as field;
//     hash.bhp256 r2 into r1713 as field;
//     hash.bhp256 r2 into r1714 as field;
//     hash.bhp256 r2 into r1715 as field;
//     hash.bhp256 r2 into r1716 as field;
//     hash.bhp256 r2 into r1717 as field;
//     hash.bhp256 r2 into r1718 as field;
//     hash.bhp256 r2 into r1719 as field;
//     hash.bhp256 r2 into r1720 as field;
//     hash.bhp256 r2 into r1721 as field;
//     hash.bhp256 r2 into r1722 as field;
//     hash.bhp256 r2 into r1723 as field;
//     hash.bhp256 r2 into r1724 as field;
//     hash.bhp256 r2 into r1725 as field;
//     hash.bhp256 r2 into r1726 as field;
//     hash.bhp256 r2 into r1727 as field;
//     hash.bhp256 r2 into r1728 as field;
//     hash.bhp256 r2 into r1729 as field;
//     hash.bhp256 r2 into r1730 as field;
//     hash.bhp256 r2 into r1731 as field;
//     hash.bhp256 r2 into r1732 as field;
//     hash.bhp256 r2 into r1733 as field;
//     hash.bhp256 r2 into r1734 as field;
//     hash.bhp256 r2 into r1735 as field;
//     hash.bhp256 r2 into r1736 as field;
//     hash.bhp256 r2 into r1737 as field;
//     hash.bhp256 r2 into r1738 as field;
//     hash.bhp256 r2 into r1739 as field;
//     hash.bhp256 r2 into r1740 as field;
//     hash.bhp256 r2 into r1741 as field;
//     hash.bhp256 r2 into r1742 as field;
//     hash.bhp256 r2 into r1743 as field;
//     hash.bhp256 r2 into r1744 as field;
//     hash.bhp256 r2 into r1745 as field;
//     hash.bhp256 r2 into r1746 as field;
//     hash.bhp256 r2 into r1747 as field;
//     hash.bhp256 r2 into r1748 as field;
//     hash.bhp256 r2 into r1749 as field;
//     hash.bhp256 r2 into r1750 as field;
//     hash.bhp256 r2 into r1751 as field;
//     hash.bhp256 r2 into r1752 as field;
//     hash.bhp256 r2 into r1753 as field;
//     hash.bhp256 r2 into r1754 as field;
//     hash.bhp256 r2 into r1755 as field;
//     hash.bhp256 r2 into r1756 as field;
//     hash.bhp256 r2 into r1757 as field;
//     hash.bhp256 r2 into r1758 as field;
//     hash.bhp256 r2 into r1759 as field;
//     hash.bhp256 r2 into r1760 as field;
//     hash.bhp256 r2 into r1761 as field;
//     hash.bhp256 r2 into r1762 as field;
//     hash.bhp256 r2 into r1763 as field;
//     hash.bhp256 r2 into r1764 as field;
//     hash.bhp256 r2 into r1765 as field;
//     hash.bhp256 r2 into r1766 as field;
//     hash.bhp256 r2 into r1767 as field;
//     hash.bhp256 r2 into r1768 as field;
//     hash.bhp256 r2 into r1769 as field;
//     hash.bhp256 r2 into r1770 as field;
//     hash.bhp256 r2 into r1771 as field;
//     hash.bhp256 r2 into r1772 as field;
//     hash.bhp256 r2 into r1773 as field;
//     hash.bhp256 r2 into r1774 as field;
//     hash.bhp256 r2 into r1775 as field;
//     hash.bhp256 r2 into r1776 as field;
//     hash.bhp256 r2 into r1777 as field;
//     hash.bhp256 r2 into r1778 as field;
//     hash.bhp256 r2 into r1779 as field;
//     hash.bhp256 r2 into r1780 as field;
//     hash.bhp256 r2 into r1781 as field;
//     hash.bhp256 r2 into r1782 as field;
//     hash.bhp256 r2 into r1783 as field;
//     hash.bhp256 r2 into r1784 as field;
//     hash.bhp256 r2 into r1785 as field;
//     hash.bhp256 r2 into r1786 as field;
//     hash.bhp256 r2 into r1787 as field;
//     hash.bhp256 r2 into r1788 as field;
//     hash.bhp256 r2 into r1789 as field;
//     hash.bhp256 r2 into r1790 as field;
//     hash.bhp256 r2 into r1791 as field;
//     hash.bhp256 r2 into r1792 as field;
//     hash.bhp256 r2 into r1793 as field;
//     hash.bhp256 r2 into r1794 as field;
//     hash.bhp256 r2 into r1795 as field;
//     hash.bhp256 r2 into r1796 as field;
//     hash.bhp256 r2 into r1797 as field;
//     hash.bhp256 r2 into r1798 as field;
//     hash.bhp256 r2 into r1799 as field;
//     hash.bhp256 r2 into r1800 as field;
//     hash.bhp256 r2 into r1801 as field;
//     hash.bhp256 r2 into r1802 as field;
//     hash.bhp256 r2 into r1803 as field;
//     hash.bhp256 r2 into r1804 as field;
//     hash.bhp256 r2 into r1805 as field;
//     hash.bhp256 r2 into r1806 as field;
//     hash.bhp256 r2 into r1807 as field;
//     hash.bhp256 r2 into r1808 as field;
//     hash.bhp256 r2 into r1809 as field;
//     hash.bhp256 r2 into r1810 as field;
//     hash.bhp256 r2 into r1811 as field;
//     hash.bhp256 r2 into r1812 as field;
//     hash.bhp256 r2 into r1813 as field;
//     hash.bhp256 r2 into r1814 as field;
//     hash.bhp256 r2 into r1815 as field;
//     hash.bhp256 r2 into r1816 as field;
//     hash.bhp256 r2 into r1817 as field;
//     hash.bhp256 r2 into r1818 as field;
//     hash.bhp256 r2 into r1819 as field;
//     hash.bhp256 r2 into r1820 as field;
//     hash.bhp256 r2 into r1821 as field;
//     hash.bhp256 r2 into r1822 as field;
//     hash.bhp256 r2 into r1823 as field;
//     hash.bhp256 r2 into r1824 as field;
//     hash.bhp256 r2 into r1825 as field;
//     hash.bhp256 r2 into r1826 as field;
//     hash.bhp256 r2 into r1827 as field;
//     hash.bhp256 r2 into r1828 as field;
//     hash.bhp256 r2 into r1829 as field;
//     hash.bhp256 r2 into r1830 as field;
//     hash.bhp256 r2 into r1831 as field;
//     hash.bhp256 r2 into r1832 as field;
//     hash.bhp256 r2 into r1833 as field;
//     hash.bhp256 r2 into r1834 as field;
//     hash.bhp256 r2 into r1835 as field;
//     hash.bhp256 r2 into r1836 as field;
//     hash.bhp256 r2 into r1837 as field;
//     hash.bhp256 r2 into r1838 as field;
//     hash.bhp256 r2 into r1839 as field;
//     hash.bhp256 r2 into r1840 as field;
//     hash.bhp256 r2 into r1841 as field;
//     hash.bhp256 r2 into r1842 as field;
//     hash.bhp256 r2 into r1843 as field;
//     hash.bhp256 r2 into r1844 as field;
//     hash.bhp256 r2 into r1845 as field;
//     hash.bhp256 r2 into r1846 as field;
//     hash.bhp256 r2 into r1847 as field;
//     hash.bhp256 r2 into r1848 as field;
//     hash.bhp256 r2 into r1849 as field;
//     hash.bhp256 r2 into r1850 as field;
//     hash.bhp256 r2 into r1851 as field;
//     hash.bhp256 r2 into r1852 as field;
//     hash.bhp256 r2 into r1853 as field;
//     hash.bhp256 r2 into r1854 as field;
//     hash.bhp256 r2 into r1855 as field;
//     hash.bhp256 r2 into r1856 as field;
//     hash.bhp256 r2 into r1857 as field;
//     hash.bhp256 r2 into r1858 as field;
//     hash.bhp256 r2 into r1859 as field;
//     hash.bhp256 r2 into r1860 as field;
//     hash.bhp256 r2 into r1861 as field;
//     hash.bhp256 r2 into r1862 as field;
//     hash.bhp256 r2 into r1863 as field;
//     hash.bhp256 r2 into r1864 as field;
//     hash.bhp256 r2 into r1865 as field;
//     hash.bhp256 r2 into r1866 as field;
//     hash.bhp256 r2 into r1867 as field;
//     hash.bhp256 r2 into r1868 as field;
//     hash.bhp256 r2 into r1869 as field;
//     hash.bhp256 r2 into r1870 as field;
//     hash.bhp256 r2 into r1871 as field;
//     hash.bhp256 r2 into r1872 as field;
//     hash.bhp256 r2 into r1873 as field;
//     hash.bhp256 r2 into r1874 as field;
//     hash.bhp256 r2 into r1875 as field;
//     hash.bhp256 r2 into r1876 as field;
//     hash.bhp256 r2 into r1877 as field;
//     hash.bhp256 r2 into r1878 as field;
//     hash.bhp256 r2 into r1879 as field;
//     hash.bhp256 r2 into r1880 as field;
//     hash.bhp256 r2 into r1881 as field;
//     hash.bhp256 r2 into r1882 as field;
//     hash.bhp256 r2 into r1883 as field;
//     hash.bhp256 r2 into r1884 as field;
//     hash.bhp256 r2 into r1885 as field;
//     hash.bhp256 r2 into r1886 as field;
//     hash.bhp256 r2 into r1887 as field;
//     hash.bhp256 r2 into r1888 as field;
//     hash.bhp256 r2 into r1889 as field;
//     hash.bhp256 r2 into r1890 as field;
//     hash.bhp256 r2 into r1891 as field;
//     hash.bhp256 r2 into r1892 as field;
//     hash.bhp256 r2 into r1893 as field;
//     hash.bhp256 r2 into r1894 as field;
//     hash.bhp256 r2 into r1895 as field;
//     hash.bhp256 r2 into r1896 as field;
//     hash.bhp256 r2 into r1897 as field;
//     hash.bhp256 r2 into r1898 as field;
//     hash.bhp256 r2 into r1899 as field;
//     hash.bhp256 r2 into r1900 as field;
//     hash.bhp256 r2 into r1901 as field;
//     hash.bhp256 r2 into r1902 as field;
//     hash.bhp256 r2 into r1903 as field;
//     hash.bhp256 r2 into r1904 as field;
//     hash.bhp256 r2 into r1905 as field;
//     hash.bhp256 r2 into r1906 as field;
//     hash.bhp256 r2 into r1907 as field;
//     hash.bhp256 r2 into r1908 as field;
//     hash.bhp256 r2 into r1909 as field;
//     hash.bhp256 r2 into r1910 as field;
//     hash.bhp256 r2 into r1911 as field;
//     hash.bhp256 r2 into r1912 as field;
//     hash.bhp256 r2 into r1913 as field;
//     hash.bhp256 r2 into r1914 as field;
//     hash.bhp256 r2 into r1915 as field;
//     hash.bhp256 r2 into r1916 as field;
//     hash.bhp256 r2 into r1917 as field;
//     hash.bhp256 r2 into r1918 as field;
//     hash.bhp256 r2 into r1919 as field;
//     hash.bhp256 r2 into r1920 as field;
//     hash.bhp256 r2 into r1921 as field;
//     hash.bhp256 r2 into r1922 as field;
//     hash.bhp256 r2 into r1923 as field;
//     hash.bhp256 r2 into r1924 as field;
//     hash.bhp256 r2 into r1925 as field;
//     hash.bhp256 r2 into r1926 as field;
//     hash.bhp256 r2 into r1927 as field;
//     hash.bhp256 r2 into r1928 as field;
//     hash.bhp256 r2 into r1929 as field;
//     hash.bhp256 r2 into r1930 as field;
//     hash.bhp256 r2 into r1931 as field;
//     hash.bhp256 r2 into r1932 as field;
//     hash.bhp256 r2 into r1933 as field;
//     hash.bhp256 r2 into r1934 as field;
//     hash.bhp256 r2 into r1935 as field;
//     hash.bhp256 r2 into r1936 as field;
//     hash.bhp256 r2 into r1937 as field;
//     hash.bhp256 r2 into r1938 as field;
//     hash.bhp256 r2 into r1939 as field;
//     hash.bhp256 r2 into r1940 as field;
//     hash.bhp256 r2 into r1941 as field;
//     hash.bhp256 r2 into r1942 as field;
//     hash.bhp256 r2 into r1943 as field;
//     hash.bhp256 r2 into r1944 as field;
//     hash.bhp256 r2 into r1945 as field;
//     hash.bhp256 r2 into r1946 as field;
//     hash.bhp256 r2 into r1947 as field;
//     hash.bhp256 r2 into r1948 as field;
//     hash.bhp256 r2 into r1949 as field;
//     hash.bhp256 r2 into r1950 as field;
//     hash.bhp256 r2 into r1951 as field;
//     hash.bhp256 r2 into r1952 as field;
//     hash.bhp256 r2 into r1953 as field;
//     hash.bhp256 r2 into r1954 as field;
//     hash.bhp256 r2 into r1955 as field;
//     hash.bhp256 r2 into r1956 as field;
//     hash.bhp256 r2 into r1957 as field;
//     hash.bhp256 r2 into r1958 as field;
//     hash.bhp256 r2 into r1959 as field;
//     hash.bhp256 r2 into r1960 as field;
//     hash.bhp256 r2 into r1961 as field;
//     hash.bhp256 r2 into r1962 as field;
//     hash.bhp256 r2 into r1963 as field;
//     hash.bhp256 r2 into r1964 as field;
//     hash.bhp256 r2 into r1965 as field;
//     hash.bhp256 r2 into r1966 as field;
//     hash.bhp256 r2 into r1967 as field;
//     hash.bhp256 r2 into r1968 as field;
//     hash.bhp256 r2 into r1969 as field;
//     hash.bhp256 r2 into r1970 as field;
//     hash.bhp256 r2 into r1971 as field;
//     hash.bhp256 r2 into r1972 as field;
//     hash.bhp256 r2 into r1973 as field;
//     hash.bhp256 r2 into r1974 as field;
//     hash.bhp256 r2 into r1975 as field;
//     hash.bhp256 r2 into r1976 as field;
//     hash.bhp256 r2 into r1977 as field;
//     hash.bhp256 r2 into r1978 as field;
//     hash.bhp256 r2 into r1979 as field;
//     hash.bhp256 r2 into r1980 as field;
//     hash.bhp256 r2 into r1981 as field;
//     hash.bhp256 r2 into r1982 as field;
//     hash.bhp256 r2 into r1983 as field;
//     hash.bhp256 r2 into r1984 as field;
//     hash.bhp256 r2 into r1985 as field;
//     hash.bhp256 r2 into r1986 as field;
//     hash.bhp256 r2 into r1987 as field;
//     hash.bhp256 r2 into r1988 as field;
//     hash.bhp256 r2 into r1989 as field;
//     hash.bhp256 r2 into r1990 as field;
//     hash.bhp256 r2 into r1991 as field;
//     hash.bhp256 r2 into r1992 as field;
//     hash.bhp256 r2 into r1993 as field;
//     hash.bhp256 r2 into r1994 as field;
//     hash.bhp256 r2 into r1995 as field;
//     hash.bhp256 r2 into r1996 as field;
//     hash.bhp256 r2 into r1997 as field;
//     hash.bhp256 r2 into r1998 as field;
//     hash.bhp256 r2 into r1999 as field;
//     hash.bhp256 r2 into r2000 as field;
//     hash.bhp256 r2 into r2001 as field;
//     hash.bhp256 r2 into r2002 as field;
//     hash.bhp256 r2 into r2003 as field;",
//         )
//         .unwrap();

//         let deployment = vm.deploy(&private_key, &program, None, 0, None, rng).unwrap();
//         vm.add_next_block(&sample_next_block(&vm, &private_key, &[deployment], rng).unwrap()).unwrap();

//         // Fetch the unspent records.
//         let records = genesis.transitions().cloned().flat_map(Transition::into_records).collect::<IndexMap<_, _>>();
//         trace!("Unspent Records:\n{:#?}", records);

//         // Select a record to spend.
//         let record = Some(records.values().next().unwrap().decrypt(&view_key).unwrap());

//         // Prepare the inputs.
//         let inputs: std::array::IntoIter<Value<CurrentNetwork>, 0> = [].into_iter(); //Value::<CurrentNetwork>::from_str("1u32").unwrap()].into_iter();

//         // Execute.
//         let transaction =
//             vm.execute(&private_key, ("program_layer_0.aleo", "do"), inputs, record, 0, None, rng).unwrap();

//         // Verify.
//         println!("check_transaction");
//         vm.check_transaction(&transaction, None, rng).unwrap();

//         // // Add next block.
//         // println!("Adding next block");
//         // // Start time measurements.
//         // let start = std::time::Instant::now();
//         // vm.add_next_block(&sample_next_block(&vm, &private_key, &[transaction], rng).unwrap()).unwrap();
//         // let duration = start.elapsed();
//         // println!("Time elapsed in add_next_block() is: {:?} ms", duration.as_millis());
//     }

//     #[test]
//     fn test_large_finalize_2() {
//         let rng = &mut TestRng::default();

//         // Initialize a private key.
//         let private_key = sample_genesis_private_key(rng);

//         // Initialize a view key.
//         let view_key = ViewKey::try_from(&private_key).unwrap();

//         // Initialize the genesis block.
//         let genesis = sample_genesis_block(rng);

//         // Initialize the VM.
//         let vm = sample_vm();
//         // Update the VM.
//         vm.add_next_block(&genesis).unwrap();

//         let mut struct_str = "".to_string();
//         // for i in 1..=40000 {
//         //     struct_str.push_str(&format!("struct m{}:\n", i));
//         //     for j in 1..=32 {
//         //         struct_str.push_str(&format!("    aaaaaaaaaaaaaaaaaaaaaaaaaaa{} as u128;\n", j));
//         //     }
//         // }

//         // use rand::{distributions::Alphanumeric, Rng};
//         let mut record_str = "".to_string();
//         // for _i in 1..=2 {
//         //     let record_id: String = rand::thread_rng()
//         //         .sample_iter(&Alphanumeric)
//         //         .take(7)
//         //         .map(char::from)
//         //         .collect();
//         //     record_str.push_str(&format!("record r{}:\n", record_id));
//         //     for j in 1..=32 {
//         //         record_str.push_str(&format!("    a{} as address.private;\n", j));
//         //     }
//         // }

//         // Deploy the base program.
//         let program_str = 
//             "program program_layer_0.aleo; function do: input r0 as field.private; hash.sha3_256 r0 into r1 as field; hash.sha3_256 r1 into r2 as field; hash.sha3_256 r2 into r3 as field; hash.sha3_256 r3 into r4 as field; hash.sha3_256 r4 into r5 as field; hash.sha3_256 r5 into r6 as field; hash.psd8 r6 into r7 as field; hash.psd8 r7 into r8 as field; hash.psd8 r8 into r9 as field; hash.psd8 r9 into r10 as field; hash.psd8 r10 into r11 as field; hash.psd8 r11 into r12 as field; hash.psd8 r12 into r13 as field; hash.psd8 r13 into r14 as field; hash.psd8 r14 into r15 as field; hash.psd8 r15 into r16 as field; hash.psd8 r16 into r17 as field; hash.psd8 r17 into r18 as field; hash.psd8 r18 into r19 as field; hash.psd8 r19 into r20 as field; hash.psd8 r20 into r21 as field; hash.psd8 r21 into r22 as field; hash.psd8 r22 into r23 as field; hash.psd8 r23 into r24 as field; hash.psd8 r24 into r25 as field; hash.psd8 r25 into r26 as field; hash.psd8 r26 into r27 as field; hash.psd8 r27 into r28 as field; hash.psd8 r28 into r29 as field; hash.psd8 r29 into r30 as field; hash.psd8 r30 into r31 as field; hash.psd8 r31 into r32 as field; hash.psd8 r32 into r33 as field; hash.psd8 r33 into r34 as field; hash.psd8 r34 into r35 as field; hash.psd8 r35 into r36 as field; hash.psd8 r36 into r37 as field; hash.psd8 r37 into r38 as field; hash.psd8 r38 into r39 as field; hash.psd8 r39 into r40 as field; hash.psd8 r40 into r41 as field; hash.psd8 r41 into r42 as field; hash.psd8 r42 into r43 as field; hash.psd8 r43 into r44 as field; hash.psd8 r44 into r45 as field; hash.psd8 r45 into r46 as field; hash.psd8 r46 into r47 as field; hash.psd8 r47 into r48 as field; hash.psd8 r48 into r49 as field; hash.psd8 r49 into r50 as field; hash.psd8 r50 into r51 as field; hash.psd8 r51 into r52 as field; hash.psd8 r52 into r53 as field; hash.psd8 r53 into r54 as field; hash.psd8 r54 into r55 as field; hash.psd8 r55 into r56 as field; hash.psd8 r56 into r57 as field; hash.psd8 r57 into r58 as field; hash.psd8 r58 into r59 as field; hash.psd8 r59 into r60 as field; hash.psd8 r60 into r61 as field; hash.psd8 r61 into r62 as field; hash.psd8 r62 into r63 as field; hash.psd8 r63 into r64 as field; hash.psd8 r64 into r65 as field; hash.psd8 r65 into r66 as field; hash.psd8 r66 into r67 as field; hash.psd8 r67 into r68 as field; hash.psd8 r68 into r69 as field; hash.psd8 r69 into r70 as field; hash.psd8 r70 into r71 as field; hash.psd8 r71 into r72 as field; hash.psd8 r72 into r73 as field; hash.psd8 r73 into r74 as field; hash.psd8 r74 into r75 as field; hash.psd8 r75 into r76 as field; hash.psd8 r76 into r77 as field; hash.psd8 r77 into r78 as field; hash.psd8 r78 into r79 as field; hash.psd8 r79 into r80 as field; hash.psd8 r80 into r81 as field; hash.psd8 r81 into r82 as field; hash.psd8 r82 into r83 as field; hash.psd8 r83 into r84 as field; hash.psd8 r84 into r85 as field; hash.psd8 r85 into r86 as field; hash.psd8 r86 into r87 as field; hash.psd8 r87 into r88 as field; hash.psd8 r88 into r89 as field; hash.psd8 r89 into r90 as field; hash.psd8 r90 into r91 as field; hash.psd8 r91 into r92 as field; hash.psd8 r92 into r93 as field; hash.psd8 r93 into r94 as field; hash.psd8 r94 into r95 as field; hash.psd8 r95 into r96 as field; output r96 as field.private;";
// //             format!(r"
// // program program_layer_0.aleo;

// // {}

// // {}

// // function do:
// //     async do into r0;
// //     output r0 as program_layer_0.aleo/do.future;

// // finalize do:
// //     cast  254u8 251u8 44u8 77u8 25u8 254u8 254u8 253u8 224u8 2u8 114u8 253u8 23u8 2u8 177u8 134u8 into r0 as [u8; 16u32];
// //     cast  r0 r0 r0 r0 r0 r0 r0 r0 r0 r0 r0 r0 r0 r0 r0 r0 into r1 as [[u8; 16u32]; 16u32];
// //     cast  r1 r1 r1 r1 r1 r1 r1 r1 into r2 as [[[u8; 16u32]; 16u32]; 8u32];
// //     hash.bhp256 r2 into r3 as field;
// //     hash.bhp256 r2 into r4 as field;", record_str, struct_str);

//         println!("program_size: {}", program_str.len());
//         println!("program: {}", program_str);

//         let program = Program::from_str(&program_str).unwrap();

//         let deployment = vm.deploy(&private_key, &program, None, 0, None, rng).unwrap();
//         println!("check_deployment");
//         vm.check_transaction(&deployment, None, rng).unwrap();
        
//         vm.add_next_block(&sample_next_block(&vm, &private_key, &[deployment], rng).unwrap()).unwrap();

//         // Fetch the unspent records.
//         let records = genesis.transitions().cloned().flat_map(Transition::into_records).collect::<IndexMap<_, _>>();
//         trace!("Unspent Records:\n{:#?}", records);

//         // Select a record to spend.
//         let record = Some(records.values().next().unwrap().decrypt(&view_key).unwrap());

//         // Prepare the inputs.
//         let inputs: std::array::IntoIter<Value<CurrentNetwork>, 0> = [].into_iter(); //Value::<CurrentNetwork>::from_str("1u32").unwrap()].into_iter();

//         // Execute.
//         let transaction =
//             vm.execute(&private_key, ("program_layer_0.aleo", "do"), inputs, record, 0, None, rng).unwrap();

//         // Verify.
//         println!("check_transaction");
//         vm.check_transaction(&transaction, None, rng).unwrap();

//         // // Add next block.
//         // println!("Adding next block");
//         // // Start time measurements.
//         // let start = std::time::Instant::now();
//         // vm.add_next_block(&sample_next_block(&vm, &private_key, &[transaction], rng).unwrap()).unwrap();
//         // let duration = start.elapsed();
//         // println!("Time elapsed in add_next_block() is: {:?} ms", duration.as_millis());
//     }
}
