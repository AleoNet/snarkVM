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

use crate::{
    ledger::{
        store::{BlockStorage, BlockStore},
        AdditionalFee,
        Transaction,
    },
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

/// A helper macro to downcast a `$variable` to `$object<$network>`.
macro_rules! cast_ref {
    // Example: cast_ref!((foo.bar()) as Bar<Testnet3>)
    (($variable:expr) as $object:ident<$($network:path),+>) => {{
        (&$variable as &dyn std::any::Any)
            .downcast_ref::<$object<$($network),+>>()
            .ok_or_else(|| anyhow!("Failed to downcast {}", stringify!($variable)))?
    }};
    // Example: cast_ref!(bar as Bar<Testnet3>)
    ($variable:ident as $object:ident<$($network:path),+>) => {{
        (&$variable as &dyn std::any::Any)
            .downcast_ref::<$object<$($network),+>>()
            .ok_or_else(|| anyhow!("Failed to downcast {}", stringify!($variable)))?
    }};
    // Example: cast_ref!(&bar as Bar<Testnet3>)
    (&$variable:ident as $object:ident<$($network:path),+>) => {{
        ($variable as &dyn std::any::Any)
            .downcast_ref::<$object<$($network),+>>()
            .ok_or_else(|| anyhow!("Failed to downcast {}", stringify!($variable)))?
    }};
}

/// A helper macro to dedup the `Network` trait and `Aleo` trait and process its given logic.
macro_rules! process {
    // Example: process!(logic)
    ($self:ident, $logic:ident) => {{
        // Process the logic.
        match N::ID {
            console::network::Testnet3::ID => {
                $logic!($self.process.read(), console::network::Testnet3, circuit::AleoV0)
            }
            _ => Err(anyhow!("Unsupported VM configuration for network: {}", N::ID)),
        }
    }};
}

/// A helper macro to dedup the `Network` trait and `Aleo` trait and process its given logic.
macro_rules! process_mut {
    // Example: process!(logic)
    ($self:ident, $logic:ident) => {{
        // Process the logic.
        match N::ID {
            console::network::Testnet3::ID => {
                $logic!($self.process.write(), console::network::Testnet3, circuit::AleoV0)
            }
            _ => Err(anyhow!("Unsupported VM configuration for network: {}", N::ID)),
        }
    }};
}

#[derive(Clone)]
pub struct VM<N: Network> {
    /// The process for Aleo Testnet3 (V0).
    process: Arc<RwLock<Process<console::network::Testnet3>>>,
    /// PhantomData.
    _phantom: PhantomData<N>,
}

impl<N: Network> VM<N> {
    /// Initializes a new VM.
    #[inline]
    pub fn new() -> Result<Self> {
        Ok(Self { process: Arc::new(RwLock::new(Process::load()?)), _phantom: PhantomData })
    }

    /// Initializes the VM from storage.
    #[inline]
    pub fn from<B: BlockStorage<N>>(blocks: &BlockStore<N, B>) -> Result<Self> {
        // Retrieve the transaction store.
        let transaction_store = blocks.transaction_store();

        // Initialize a new process.
        let mut process = Process::load()?;

        // Load the deployments from the store.
        for program in transaction_store.programs() {
            // Add the program to the process.
            process.add_program(&*program)?;

            // Retrieve the program ID.
            let program_id = program.id();
            // Iterate through the function names.
            for function_name in program.functions().keys() {
                // Retrieve the verifying key for the function.
                match transaction_store.get_verifying_key(program_id, function_name)? {
                    // Add the verifying key to the process.
                    Some(verifying_key) => process.insert_verifying_key(program_id, function_name, verifying_key)?,
                    // Throw an error if the verifying key is not found.
                    None => bail!("Missing a verifying key in storage for {program_id}/{function_name}"),
                }
            }
        }

        // Cast the process into the appropriate network.
        macro_rules! logic {
            ($process:expr, $network:path, $aleo:path) => {{
                // Prepare the process.
                let process = cast_ref!(process as Process<$network>);

                // Return the new VM.
                Ok(Self { process: Arc::new(RwLock::new((*process).clone())), _phantom: PhantomData })
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

    /// Deploys a program with the given program ID.
    #[inline]
    pub fn deploy<R: Rng + CryptoRng>(&self, program: &Program<N>, rng: &mut R) -> Result<Deployment<N>> {
        // Compute the core logic.
        macro_rules! logic {
            ($process:expr, $network:path, $aleo:path) => {{
                // Prepare the program.
                let program = cast_ref!(&program as Program<$network>);

                // Compute the deployment.
                let deployment = $process.deploy::<$aleo, _>(program, rng)?;

                // Prepare the return.
                let deployment = cast_ref!(deployment as Deployment<N>).clone();
                // Return the deployment.
                Ok(deployment)
            }};
        }
        // Process the logic.
        process!(self, logic)
    }

    /// Authorizes a call to the program function for the given inputs.
    #[inline]
    pub fn authorize<R: Rng + CryptoRng>(
        &self,
        private_key: &PrivateKey<N>,
        program_id: &ProgramID<N>,
        function_name: Identifier<N>,
        inputs: &[Value<N>],
        rng: &mut R,
    ) -> Result<Authorization<N>> {
        // Compute the core logic.
        macro_rules! logic {
            ($process:expr, $network:path, $aleo:path) => {{
                let inputs = inputs.to_vec();

                // Prepare the inputs.
                let private_key = cast_ref!(&private_key as PrivateKey<$network>);
                let program_id = cast_ref!(&program_id as ProgramID<$network>);
                let function_name = cast_ref!(function_name as Identifier<$network>);
                let inputs = cast_ref!(inputs as Vec<Value<$network>>);

                // Compute the authorization.
                let authorization =
                    $process.authorize::<$aleo, _>(private_key, program_id, function_name.clone(), inputs, rng)?;

                // Return the authorization.
                Ok(cast_ref!(authorization as Authorization<N>).clone())
            }};
        }
        // Process the logic.
        process!(self, logic)
    }

    /// Executes a call to the program function for the given inputs.
    #[inline]
    pub fn execute<R: Rng + CryptoRng>(
        &self,
        authorization: Authorization<N>,
        rng: &mut R,
    ) -> Result<(Response<N>, Execution<N>)> {
        // Compute the core logic.
        macro_rules! logic {
            ($process:expr, $network:path, $aleo:path) => {{
                // Prepare the authorization.
                let authorization = cast_ref!(authorization as Authorization<$network>);

                // Execute the call.
                let (response, execution) = $process.execute::<$aleo, _>(authorization.clone(), rng)?;

                // Prepare the return.
                let response = cast_ref!(response as Response<N>).clone();
                let execution = cast_ref!(execution as Execution<N>).clone();
                // Return the response and execution.
                Ok((response, execution))
            }};
        }
        // Process the logic.
        process!(self, logic)
    }

    /// Returns an additional fee for the given private key, credits record, and additional fee amount (in gates).
    #[inline]
    pub fn execute_additional_fee<R: Rng + CryptoRng>(
        &self,
        private_key: &PrivateKey<N>,
        credits: Record<N, Plaintext<N>>,
        additional_fee_in_gates: u64,
        rng: &mut R,
    ) -> Result<(Response<N>, AdditionalFee<N>)> {
        // Compute the core logic.
        macro_rules! logic {
            ($process:expr, $network:path, $aleo:path) => {{
                type RecordPlaintext<NetworkMacro> = Record<NetworkMacro, Plaintext<NetworkMacro>>;

                // Prepare the private key and credits record.
                let private_key = cast_ref!(&private_key as PrivateKey<$network>);
                let credits = cast_ref!(credits as RecordPlaintext<$network>);

                // Execute the call to additional fee.
                let (response, additional_fee) = $process.execute_additional_fee::<$aleo, _>(
                    private_key,
                    credits.clone(),
                    additional_fee_in_gates,
                    rng,
                )?;

                // Prepare the return.
                let response = cast_ref!(response as Response<N>).clone();
                let additional_fee = cast_ref!(additional_fee as AdditionalFee<N>).clone();
                // Return the response and additional fee.
                Ok((response, additional_fee))
            }};
        }
        // Process the logic.
        process!(self, logic)
    }

    /// Verifies the transaction in the VM.
    #[inline]
    pub fn verify(&self, transaction: &Transaction<N>) -> bool {
        // Compute the Merkle root of the transaction.
        match transaction.to_root() {
            // Ensure the transaction ID is correct.
            Ok(root) => {
                if *transaction.id() != root {
                    warn!("Incorrect transaction ID ({})", transaction.id());
                    return false;
                }
            }
            Err(error) => {
                warn!("Failed to compute the Merkle root of the transaction: {error}\n{transaction}");
                return false;
            }
        };

        // Ensure there are no duplicate transition IDs.
        if has_duplicates(transaction.transition_ids()) {
            warn!("Found duplicate transition in the transactions list");
            return false;
        }

        // Ensure there are no duplicate transition public keys.
        if has_duplicates(transaction.transition_public_keys()) {
            warn!("Found duplicate transition public keys in the transactions list");
            return false;
        }

        // Ensure there are no duplicate serial numbers.
        if has_duplicates(transaction.serial_numbers()) {
            warn!("Found duplicate serial numbers in the transactions list");
            return false;
        }

        // Ensure there are no duplicate commitments.
        if has_duplicates(transaction.commitments()) {
            warn!("Found duplicate commitments in the transactions list");
            return false;
        }

        // Ensure there are no duplicate nonces.
        if has_duplicates(transaction.nonces()) {
            warn!("Found duplicate nonces in the transactions list");
            return false;
        }

        match transaction {
            Transaction::Deploy(_, deployment, additional_fee) => {
                // Check the deployment size.
                if let Err(error) = Transaction::check_deployment_size(deployment) {
                    warn!("Invalid transaction size (deployment): {error}");
                    return false;
                }
                // Verify the deployment.
                self.verify_deployment(deployment)
                    // Verify the additional fee.
                    && self.verify_additional_fee(additional_fee)
            }
            Transaction::Execute(_, execution, additional_fee) => {
                // Check the deployment size.
                if let Err(error) = Transaction::check_execution_size(execution) {
                    warn!("Invalid transaction size (execution): {error}");
                    return false;
                }

                // Verify the additional fee, if it exists.
                let check_additional_fee = match additional_fee {
                    Some(additional_fee) => self.verify_additional_fee(additional_fee),
                    None => true,
                };

                // Verify the execution.
                self.verify_execution(execution)
                    // Verify the additional fee.
                    && check_additional_fee
            }
        }
    }

    /// Verifies the given deployment.
    #[inline]
    fn verify_deployment(&self, deployment: &Deployment<N>) -> bool {
        // Compute the core logic.
        macro_rules! logic {
            ($process:expr, $network:path, $aleo:path) => {{
                let task = || {
                    // Prepare the deployment.
                    let deployment = cast_ref!(&deployment as Deployment<$network>);
                    // Initialize an RNG.
                    let rng = &mut rand::thread_rng();
                    // Verify the deployment.
                    $process.verify_deployment::<$aleo, _>(&deployment, rng)
                };
                task()
            }};
        }

        // Process the logic.
        match process!(self, logic) {
            Ok(()) => true,
            Err(error) => {
                warn!("Deployment verification failed: {error}");
                false
            }
        }
    }

    /// Verifies the given execution.
    #[inline]
    fn verify_execution(&self, execution: &Execution<N>) -> bool {
        // Compute the core logic.
        macro_rules! logic {
            ($process:expr, $network:path, $aleo:path) => {{
                let task = || {
                    // Prepare the execution.
                    let execution = cast_ref!(&execution as Execution<$network>);
                    // Verify the execution.
                    $process.verify_execution(execution)
                };
                task()
            }};
        }

        // Process the logic.
        match process!(self, logic) {
            Ok(()) => true,
            Err(error) => {
                warn!("Execution verification failed: {error}");
                false
            }
        }
    }

    /// Verifies the given additional fee.
    #[inline]
    fn verify_additional_fee(&self, additional_fee: &AdditionalFee<N>) -> bool {
        // Compute the core logic.
        macro_rules! logic {
            ($process:expr, $network:path, $aleo:path) => {{
                let task = || {
                    // Prepare the additional fee.
                    let additional_fee = cast_ref!(&additional_fee as AdditionalFee<$network>);
                    // Verify the additional fee.
                    $process.verify_additional_fee(additional_fee)
                };
                task()
            }};
        }

        // Process the logic.
        match process!(self, logic) {
            Ok(()) => true,
            Err(error) => {
                warn!("Additional fee verification failed: {error}");
                false
            }
        }
    }

    /// Finalizes the transaction into the VM.
    /// This method assumes the given transaction **is valid**.
    #[inline]
    pub fn finalize(&mut self, transaction: &Transaction<N>) -> Result<()> {
        // Ensure the transaction is valid.
        ensure!(self.verify(transaction), "Invalid transaction: failed to verify");
        // Finalize the transaction.
        match transaction {
            Transaction::Deploy(_, deployment, _) => self.finalize_deployment(deployment),
            Transaction::Execute(_, _execution, _) => Ok(()), // self.finalize_execution(execution),
        }
    }

    /// Adds the newly-deployed program into the VM.
    #[inline]
    fn finalize_deployment(&mut self, deployment: &Deployment<N>) -> Result<()> {
        // Compute the core logic.
        macro_rules! logic {
            ($process:expr, $network:path, $aleo:path) => {{
                // Prepare the deployment.
                let deployment = cast_ref!(&deployment as Deployment<$network>);
                // Add the program.
                $process.add_program(deployment.program())?;
                // Insert the verifying keys.
                for (function_name, (verifying_key, _)) in deployment.verifying_keys() {
                    $process.insert_verifying_key(deployment.program().id(), function_name, verifying_key.clone())?;
                }
                Ok(())
            }};
        }
        // Process the logic.
        process_mut!(self, logic)
    }
}

#[cfg(test)]
pub(crate) mod test_helpers {
    use super::*;
    use crate::{program::Program, RecordsFilter};
    use console::{
        account::{Address, ViewKey},
        network::Testnet3,
        program::{Identifier, Value},
    };

    use once_cell::sync::OnceCell;

    type CurrentNetwork = Testnet3;

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

    pub(crate) fn sample_deployment_transaction() -> Transaction<CurrentNetwork> {
        static INSTANCE: OnceCell<Transaction<CurrentNetwork>> = OnceCell::new();
        INSTANCE
            .get_or_init(|| {
                // Initialize the program.
                let program = sample_program();

                // Initialize a new caller.
                let caller_private_key = crate::ledger::test_helpers::sample_genesis_private_key();
                let caller_view_key = ViewKey::try_from(&caller_private_key).unwrap();

                // Initialize the ledger.
                let ledger = crate::ledger::test_helpers::sample_genesis_ledger();

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

                // Initialize the RNG.
                let rng = &mut test_crypto_rng();
                // Initialize the VM.
                let vm = VM::<CurrentNetwork>::new().unwrap();
                // Deploy.
                let transaction = Transaction::deploy(&vm, &caller_private_key, &program, additional_fee, rng).unwrap();
                // Verify.
                assert!(vm.verify(&transaction));
                // Return the transaction.
                transaction
            })
            .clone()
    }

    pub(crate) fn sample_execution_transaction() -> Transaction<CurrentNetwork> {
        static INSTANCE: OnceCell<Transaction<CurrentNetwork>> = OnceCell::new();
        INSTANCE
            .get_or_init(|| {
                // Initialize a new caller.
                let caller_private_key = crate::ledger::test_helpers::sample_genesis_private_key();
                let caller_view_key = ViewKey::try_from(&caller_private_key).unwrap();
                let address = Address::try_from(&caller_private_key).unwrap();

                // Initialize the ledger.
                let ledger = crate::ledger::test_helpers::sample_genesis_ledger();

                // Fetch the unspent records.
                let records = ledger
                    .find_records(&caller_view_key, RecordsFilter::SlowUnspent(caller_private_key))
                    .unwrap()
                    .filter(|(_, record)| !record.gates().is_zero())
                    .collect::<indexmap::IndexMap<_, _>>();
                trace!("Unspent Records:\n{:#?}", records);
                // Select a record to spend.
                let record = records.values().next().unwrap().clone();

                // Initialize the RNG.
                let rng = &mut test_crypto_rng();
                // Initialize the VM.
                let vm = VM::<CurrentNetwork>::new().unwrap();

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

#[cfg(test)]
mod tests {
    use crate::{ledger::vm::test_helpers::sample_program, VM};
    use console::network::Testnet3;
    use snarkvm_utilities::test_crypto_rng;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_verify() {
        let vm = VM::<CurrentNetwork>::new().unwrap();

        // Fetch a deployment transaction.
        let deployment_transaction = crate::ledger::vm::test_helpers::sample_deployment_transaction();
        // Ensure the transaction verifies.
        assert!(vm.verify(&deployment_transaction));

        // Fetch a execution transaction.
        let execution_transaction = crate::ledger::vm::test_helpers::sample_execution_transaction();
        // Ensure the transaction verifies.
        assert!(vm.verify(&execution_transaction));
    }

    #[test]
    fn test_verify_deployment() {
        let rng = &mut test_crypto_rng();
        let vm = VM::<CurrentNetwork>::new().unwrap();

        // Fetch the program from the deployment.
        let program = sample_program();

        // Deploy the program.
        let deployment = vm.deploy(&program, rng).unwrap();

        // Ensure the deployment is valid.
        assert!(vm.verify_deployment(&deployment));
    }

    #[test]
    fn test_finalize() {
        let mut vm = VM::<CurrentNetwork>::new().unwrap();

        // Fetch a deployment transaction.
        let deployment_transaction = crate::ledger::vm::test_helpers::sample_deployment_transaction();

        // Finalize the transaction.
        vm.finalize(&deployment_transaction).unwrap();

        // Ensure the VM can't redeploy the same transaction.
        assert!(vm.finalize(&deployment_transaction).is_err());
    }

    #[test]
    fn test_finalize_deployment() {
        let rng = &mut test_crypto_rng();
        let mut vm = VM::<CurrentNetwork>::new().unwrap();

        // Fetch the program from the deployment.
        let program = sample_program();

        // Deploy the program.
        let deployment = vm.deploy(&program, rng).unwrap();

        // Ensure the program does not exists.
        assert!(!vm.contains_program(program.id()));

        // Finalize the deployment.
        vm.finalize_deployment(&deployment).unwrap();

        // Ensure the program exists.
        assert!(vm.contains_program(program.id()));
    }
}
