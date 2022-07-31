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
    ledger::{AdditionalFee, Transaction},
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
    (($variable:expr) as $object:ident<$network:path>) => {{
        (&$variable as &dyn std::any::Any)
            .downcast_ref::<$object<$network>>()
            .ok_or_else(|| anyhow!("Failed to downcast {}", stringify!($variable)))?
    }};
    // Example: cast_ref!(bar as Bar<Testnet3>)
    ($variable:ident as $object:ident<$network:path>) => {{
        (&$variable as &dyn std::any::Any)
            .downcast_ref::<$object<$network>>()
            .ok_or_else(|| anyhow!("Failed to downcast {}", stringify!($variable)))?
    }};
    // Example: cast_ref!(&bar as Bar<Testnet3>)
    (&$variable:ident as $object:ident<$network:path>) => {{
        ($variable as &dyn std::any::Any)
            .downcast_ref::<$object<$network>>()
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
        Ok(Self { process: Arc::new(RwLock::new(Process::new()?)), _phantom: PhantomData })
    }

    /// Synthesizes the proving and verifying key for the given credit program.
    #[inline]
    pub fn synthesize_credit_program_keys<
        A: circuit::Aleo<Network = console::network::Testnet3>,
        R: Rng + CryptoRng,
    >(
        &self,
        rng: &mut R,
    ) -> Result<()> {
        self.process.write().synthesize_credit_program_keys::<A, R>(rng)
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

    /// Adds a new program to the VM.
    pub fn on_deploy(&mut self, transaction: &Transaction<N>) -> Result<()> {
        // Ensure the transaction is a deployment.
        ensure!(matches!(transaction, Transaction::Deploy(..)), "Invalid transaction type: expected a deployment");
        // Ensure the transaction is valid.
        ensure!(transaction.verify(self), "Invalid transaction: failed to verify");

        // Compute the core logic.
        macro_rules! logic {
            ($process:expr, $network:path, $aleo:path) => {{
                // Prepare the transaction.
                let transaction = cast_ref!(&transaction as Transaction<$network>);
                // Deploy the program.
                if let Transaction::Deploy(_, deployment, _) = transaction {
                    // Add the program.
                    $process.add_program(deployment.program())?;
                    // Insert the verifying keys.
                    for (function_name, (verifying_key, _)) in deployment.verifying_keys() {
                        $process.insert_verifying_key(
                            deployment.program().id(),
                            function_name,
                            verifying_key.clone(),
                        )?;
                    }
                }
                Ok(())
            }};
        }
        // Process the logic.
        process_mut!(self, logic)
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

    /// Verifies the given deployment.
    #[inline]
    pub fn verify_deployment(&self, deployment: &Deployment<N>) -> bool {
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
                eprintln!("Deployment verification failed: {error}");
                warn!("Deployment verification failed: {error}");
                false
            }
        }
    }

    /// Verifies the given execution.
    #[inline]
    pub fn verify_execution(&self, execution: &Execution<N>) -> bool {
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
                eprintln!("Execution verification failed: {error}");
                warn!("Execution verification failed: {error}");
                false
            }
        }
    }

    /// Verifies the given additional fee.
    #[inline]
    pub fn verify_additional_fee(&self, additional_fee: &AdditionalFee<N>) -> bool {
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
                eprintln!("Additional fee verification failed: {error}");
                warn!("Additional fee verification failed: {error}");
                false
            }
        }
    }
}

#[cfg(test)]
pub(crate) mod test_helpers {
    use super::*;
    use crate::{
        ledger::{Block, Transition},
        program::Program,
    };
    use console::{
        account::{Address, PrivateKey},
        network::Testnet3,
        program::{Identifier, Value},
    };
    use snarkvm_utilities::test_crypto_rng_fixed;

    use once_cell::sync::OnceCell;

    type CurrentNetwork = Testnet3;
    type CurrentAleo = circuit::AleoV0;

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

    pub(crate) fn sample_vm() -> VM<CurrentNetwork> {
        static INSTANCE: OnceCell<VM<CurrentNetwork>> = OnceCell::new();
        INSTANCE
            .get_or_init(|| {
                let rng = &mut test_crypto_rng_fixed();

                // Initialize a new VM.
                let vm = VM::<CurrentNetwork>::new().unwrap();
                vm.synthesize_credit_program_keys::<CurrentAleo, _>(rng).unwrap();

                vm
            })
            .clone()
    }

    pub(crate) fn sample_deployment_transaction() -> Transaction<CurrentNetwork> {
        static INSTANCE: OnceCell<Transaction<CurrentNetwork>> = OnceCell::new();
        INSTANCE
            .get_or_init(|| {
                // Initialize the VM.
                let vm = sample_vm();
                // Initialize the program.
                let program = sample_program();

                // Initialize the RNG.
                let rng = &mut test_crypto_rng();
                // Initialize a new caller.

                let caller_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
                let address = Address::try_from(&caller_private_key).unwrap();
                // Prepare the additional fee.
                let credits =
                    Record::from_str(&format!("{{ owner: {address}.private, gates: 10u64.private }}")).unwrap();
                let additional_fee = (credits, 10);

                // Deploy.
                let transaction = Transaction::deploy(&vm, &caller_private_key, &program, additional_fee, rng).unwrap();
                // Verify.
                assert!(transaction.verify(&vm));
                // Return the transaction.
                transaction
            })
            .clone()
    }

    pub(crate) fn sample_execution_transaction() -> Transaction<CurrentNetwork> {
        static INSTANCE: OnceCell<Transaction<CurrentNetwork>> = OnceCell::new();
        INSTANCE
            .get_or_init(|| {
                // Initialize the VM.
                let mut vm = sample_vm();
                // Deploy the program.
                let transaction = sample_deployment_transaction();
                // On Deploy.
                vm.on_deploy(&transaction).unwrap();

                // Initialize the RNG.
                let rng = &mut test_crypto_rng();
                // Initialize a new caller.
                let caller_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
                let address = Address::try_from(&caller_private_key).unwrap();
                // Authorize.
                let authorization = vm
                    .authorize(
                        &caller_private_key,
                        &ProgramID::from_str("testing.aleo").unwrap(),
                        Identifier::from_str("compute").unwrap(),
                        &[
                            Value::<CurrentNetwork>::from_str("{ amount: 9876543210u128 }").unwrap(),
                            Value::<CurrentNetwork>::from_str("{ amount: 9876543210u128 }").unwrap(),
                            Value::<CurrentNetwork>::from_str("{ amount: 9876543210u128 }").unwrap(),
                            Value::<CurrentNetwork>::from_str(&format!(
                                "{{ owner: {address}.private, gates: 5u64.private, amount: 100u64.private }}"
                            ))
                            .unwrap(),
                        ],
                        rng,
                    )
                    .unwrap();
                assert_eq!(authorization.len(), 1);

                // Execute.
                let transaction = Transaction::execute_authorization(&vm, authorization, rng).unwrap();
                // Verify.
                assert!(transaction.verify(&vm));
                // Return the transaction.
                transaction
            })
            .clone()
    }

    pub(crate) fn sample_genesis_block() -> Block<CurrentNetwork> {
        static INSTANCE: OnceCell<Block<CurrentNetwork>> = OnceCell::new();
        INSTANCE
            .get_or_init(|| {
                // Initialize the VM.
                let mut vm = VM::<CurrentNetwork>::new().unwrap();
                // Initialize the RNG.
                let rng = &mut test_crypto_rng_fixed();
                // Initialize a new caller.
                let caller_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
                // Return the block.
                Block::genesis(&mut vm, &caller_private_key, rng).unwrap()
            })
            .clone()
    }

    #[allow(dead_code)]
    pub(crate) fn sample_transition() -> Transition<CurrentNetwork> {
        // Retrieve the transaction.
        let transaction = sample_execution_transaction();
        // Retrieve the transitions.
        let mut transitions = transaction.transitions();
        // Return a transition.
        transitions.next().cloned().unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_utilities::test_crypto_rng;

    use crate::ledger::vm::test_helpers::{sample_deployment_transaction, sample_vm};

    #[test]
    fn test_vm_deploy() {
        let rng = &mut test_crypto_rng();
        let vm = sample_vm();

        // Fetch the program from the deployment.
        let deployment = if let Transaction::Deploy(_, deployment, _) = sample_deployment_transaction() {
            Some(deployment)
        } else {
            None
        }
        .unwrap();

        let program = deployment.program();

        // Deploy the program.
        let deployment = vm.deploy(program, rng).unwrap();

        // Ensure the deployment is valid.
        assert!(vm.verify_deployment(&deployment));
    }

    #[test]
    fn test_vm_on_deploy() {
        let mut vm = sample_vm();

        // Fetch a deployment transaction.
        let deployment_transaction = sample_deployment_transaction();

        // Deploy the transaction.
        vm.on_deploy(&deployment_transaction).unwrap();

        // Ensure the VM can't redeploy the same transaction.
        assert!(vm.on_deploy(&deployment_transaction).is_err());
    }
}
