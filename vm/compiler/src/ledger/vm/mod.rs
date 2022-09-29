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
    cast_ref,
    ledger::{
        store::{BlockStorage, BlockStore, ProgramStorage, ProgramStore},
        AdditionalFee,
        Transaction,
    },
    process,
    process::{Authorization, Deployment, Execution, Process},
    program::Program,
};
use console::{
    account::PrivateKey,
    network::prelude::*,
    program::{Identifier, Plaintext, ProgramID, Record, Response, Value},
};

use core::marker::PhantomData;
use parking_lot::RwLock;
use std::sync::Arc;

#[derive(Clone)]
pub struct VM<N: Network, P: ProgramStorage<N>> {
    /// The process for Aleo Testnet3 (V0).
    process: Arc<RwLock<Process<console::network::Testnet3>>>,
    /// The program store.
    store: ProgramStore<N, P>,
    /// PhantomData.
    _phantom: PhantomData<N>,
}

impl<N: Network, P: ProgramStorage<N>> VM<N, P> {
    /// Initializes a new VM.
    #[inline]
    pub fn new(store: ProgramStore<N, P>) -> Result<Self> {
        Ok(Self { process: Arc::new(RwLock::new(Process::load()?)), store, _phantom: PhantomData })
    }

    /// Initializes the VM from storage.
    #[inline]
    pub fn from<B: BlockStorage<N>>(blocks: &BlockStore<N, B>, store: ProgramStore<N, P>) -> Result<Self> {
        // Retrieve the transaction store.
        let transaction_store = blocks.transaction_store();

        // Initialize a new process.
        let mut process = Process::load()?;

        // Load the deployments from the store.
        for transaction_id in transaction_store.deployment_ids() {
            // Retrieve the deployment.
            match transaction_store.get_deployment(&transaction_id)? {
                // Load the deployment.
                Some(deployment) => process.load_deployment(&deployment)?,
                None => bail!("Deployment transaction '{transaction_id}' is not found in storage."),
            };
        }

        // Cast the process into the appropriate network.
        macro_rules! logic {
            ($process:expr, $network:path, $aleo:path) => {{
                // Prepare the process.
                let process = cast_ref!(process as Process<$network>);

                // Return the new VM.
                Ok(Self { process: Arc::new(RwLock::new((*process).clone())), store, _phantom: PhantomData })
            }};
        }
        // Process the logic.
        process!(self, logic)
    }

    /// Deploys a program with the given program ID.
    #[inline]
    pub fn contains_program(&self, program_id: &ProgramID<N>) -> bool {
        // Compute the core logic.
        macro_rules! logic {
            ($process:expr, $network:path, $aleo:path) => {{
                let task = || {
                    // Prepare the program ID.
                    let program_id = cast_ref!(&program_id as ProgramID<$network>);
                    // Return `true` if the program ID exists.
                    Ok($process.contains_program(program_id))
                };
                task()
            }};
        }
        // Process the logic.
        match process!(self, logic) {
            Ok(contains_program) => contains_program,
            Err(error) => {
                warn!("Failed to check if program exists: {error}");
                false
            }
        }
    }
}

#[cfg(test)]
pub(crate) mod test_helpers {
    use super::*;
    use crate::{program::Program, ProgramMemory, RecordsFilter};
    use console::{
        account::{Address, ViewKey},
        network::Testnet3,
        program::{Identifier, Value},
    };

    use once_cell::sync::OnceCell;

    type CurrentNetwork = Testnet3;

    pub(crate) fn sample_vm() -> VM<CurrentNetwork, ProgramMemory<CurrentNetwork>> {
        VM::new(ProgramStore::open(None).unwrap()).unwrap()
    }

    pub(crate) fn sample_program() -> Program<CurrentNetwork> {
        static INSTANCE: OnceCell<Program<CurrentNetwork>> = OnceCell::new();
        INSTANCE
            .get_or_init(|| {
                // Initialize a new program.
                Program::<CurrentNetwork>::from_str(
                    r"
program testing.aleo;

interface message:
    amount as u128;

record token:
    owner as address.private;
    gates as u64.private;
    amount as u64.private;

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
                let caller_private_key = crate::ledger::test_helpers::sample_genesis_private_key(rng);
                let caller_view_key = ViewKey::try_from(&caller_private_key).unwrap();

                // Initialize the ledger.
                let ledger = crate::ledger::test_helpers::sample_genesis_ledger(rng);

                // Fetch the unspent records.
                let records = ledger
                    .find_records(&caller_view_key, RecordsFilter::SlowUnspent(caller_private_key))
                    .unwrap()
                    .filter(|(_, record)| !record.gates().is_zero())
                    .collect::<indexmap::IndexMap<_, _>>();
                trace!("Unspent Records:\n{:#?}", records);

                // Prepare the additional fee.
                let credits = records.values().next().unwrap().clone();
                let additional_fee = (credits, 10);

                // Initialize the VM.
                let vm = sample_vm();
                // Deploy.
                let transaction = Transaction::deploy(&vm, &caller_private_key, &program, additional_fee, rng).unwrap();
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
                let caller_private_key = crate::ledger::test_helpers::sample_genesis_private_key(rng);
                let caller_view_key = ViewKey::try_from(&caller_private_key).unwrap();
                let address = Address::try_from(&caller_private_key).unwrap();

                // Initialize the ledger.
                let ledger = crate::ledger::test_helpers::sample_genesis_ledger(rng);

                // Fetch the unspent records.
                let records = ledger
                    .find_records(&caller_view_key, RecordsFilter::SlowUnspent(caller_private_key))
                    .unwrap()
                    .filter(|(_, record)| !record.gates().is_zero())
                    .collect::<indexmap::IndexMap<_, _>>();
                trace!("Unspent Records:\n{:#?}", records);
                // Select a record to spend.
                let record = records.values().next().unwrap().clone();

                // Initialize the VM.
                let vm = sample_vm();

                // Authorize.
                let authorization = vm
                    .authorize(
                        &caller_private_key,
                        &ProgramID::from_str("credits.aleo").unwrap(),
                        Identifier::from_str("transfer").unwrap(),
                        &[
                            Value::<CurrentNetwork>::Record(record),
                            Value::<CurrentNetwork>::from_str(&address.to_string()).unwrap(),
                            Value::<CurrentNetwork>::from_str("1u64").unwrap(),
                        ],
                        rng,
                    )
                    .unwrap();
                assert_eq!(authorization.len(), 1);

                // Execute.
                let transaction = Transaction::execute_authorization(&vm, authorization, rng).unwrap();
                // Verify.
                assert!(vm.verify(&transaction));
                // Return the transaction.
                transaction
            })
            .clone()
    }
}
