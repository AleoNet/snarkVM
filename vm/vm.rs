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
    console::{
        account::PrivateKey,
        network::prelude::*,
        program::{Identifier, ProgramID, Response, Value},
    },
    ledger::Transaction,
};
use snarkvm_compiler::{Authorization, Deployment, Execution, Process, Program};

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

lazy_static! {
    /// The process for Aleo Testnet3 (V0).
    pub(crate) static ref TESTNET3_V0: Arc<RwLock<Process<crate::prelude::Testnet3>>> = Arc::new(RwLock::new(Process::new()));
}

/// A helper macro to dedup the `Network` trait and `Aleo` trait and process its given logic.
macro_rules! process {
    // Example: process!(logic)
    ($logic:ident) => {{
        // Process the logic.
        match N::ID {
            crate::prelude::Testnet3::ID => {
                $logic!(TESTNET3_V0.read(), crate::prelude::Testnet3, crate::circuit::AleoV0)
            }
            _ => Err(anyhow!("Unsupported VM configuration for network: {}", N::ID)),
        }
    }};
}

/// A helper macro to dedup the `Network` trait and `Aleo` trait and process its given logic.
macro_rules! process_mut {
    // Example: process!(logic)
    ($logic:ident) => {{
        // Process the logic.
        match N::ID {
            crate::prelude::Testnet3::ID => {
                $logic!(TESTNET3_V0.write(), crate::prelude::Testnet3, crate::circuit::AleoV0)
            }
            _ => Err(anyhow!("Unsupported VM configuration for network: {}", N::ID)),
        }
    }};
}

pub struct VM;

impl VM {
    /// Adds a new program to the VM.
    #[inline]
    pub fn add_program<N: Network>(program: &Program<N>) -> Result<()> {
        // Compute the core logic.
        macro_rules! logic {
            ($process:expr, $network:path, $aleo:path) => {{
                // Prepare the program.
                let program = cast_ref!(&program as Program<$network>);
                // Add the program.
                $process.add_program(program)
            }};
        }
        // Process the logic.
        process_mut!(logic)
    }

    /// Deploys a program with the given program ID.
    #[inline]
    pub fn deploy<N: Network, R: Rng + CryptoRng>(program_id: &ProgramID<N>, rng: &mut R) -> Result<Transaction<N>> {
        // Compute the core logic.
        macro_rules! logic {
            ($process:expr, $network:path, $aleo:path) => {{
                // Prepare the program ID.
                let program_id = cast_ref!(&program_id as ProgramID<$network>);

                // Compute the deployment.
                let deployment = $process.deploy::<$aleo, _>(program_id, rng)?;
                // Construct the transaction.
                let transaction = Transaction::deploy(deployment)?;

                // Prepare the return.
                let transaction = cast_ref!(transaction as Transaction<N>).clone();
                // Return the transaction.
                Ok(transaction)
            }};
        }
        // Process the logic.
        process!(logic)
    }

    /// Authorizes a call to the program function for the given inputs.
    #[inline]
    pub fn authorize<N: Network, R: Rng + CryptoRng>(
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
        process!(logic)
    }

    /// Executes a call to the program function for the given inputs.
    #[inline]
    pub fn execute<N: Network, R: Rng + CryptoRng>(
        authorization: Authorization<N>,
        rng: &mut R,
    ) -> Result<(Response<N>, Transaction<N>)> {
        // Compute the core logic.
        macro_rules! logic {
            ($process:expr, $network:path, $aleo:path) => {{
                // Prepare the authorization.
                let authorization = cast_ref!(authorization as Authorization<$network>);

                // Execute the call.
                let (response, execution) = $process.execute::<$aleo, _>(authorization.clone(), rng)?;
                // Construct the transaction.
                let transaction = Transaction::execute(execution)?;

                // Prepare the return.
                let response = cast_ref!(response as Response<N>).clone();
                let transaction = cast_ref!(transaction as Transaction<N>).clone();
                // Return the response and transaction.
                Ok((response, transaction))
            }};
        }
        // Process the logic.
        process!(logic)
    }

    /// Verifies a program call for the given execution.
    #[inline]
    pub fn verify<N: Network>(transaction: &Transaction<N>) -> bool {
        // Compute the Merkle root of the transaction.
        match transaction.to_root() {
            // Ensure the transaction ID is correct.
            Ok(transaction_root) => {
                if *transaction.id() != transaction_root {
                    warn!("Incorrect transaction ID ({})", transaction.id());
                    return false;
                }
            }
            Err(error) => {
                warn!("Failed to compute the Merkle root of the transaction: {transaction} {error}");
                return false;
            }
        };

        match transaction {
            Transaction::Deploy(_, deployment) => {
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
                match process!(logic) {
                    Ok(()) => true,
                    Err(error) => {
                        warn!("Transaction (deployment) verification failed: {error}");
                        false
                    }
                }
            }
            Transaction::Execute(_, execution) => {
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
                match process!(logic) {
                    Ok(()) => true,
                    Err(error) => {
                        warn!("Transaction (execution) verification failed: {error}");
                        false
                    }
                }
            }
        }
    }
}

#[cfg(test)]
pub(crate) mod test_helpers {
    use super::*;
    use crate::console::{
        account::{Address, PrivateKey},
        network::Testnet3,
        program::{Identifier, Value},
    };
    use snarkvm_compiler::{Program, Transition};

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
                // Initialize a new program.
                let program = sample_program();
                // Add the program.
                VM::add_program(&program).unwrap();

                // Initialize the RNG.
                let rng = &mut test_crypto_rng();
                // Deploy.
                let transaction = VM::deploy(program.id(), rng).unwrap();
                // Verify.
                assert!(VM::verify(&transaction));
                // Return the transaction.
                transaction
            })
            .clone()
    }

    pub(crate) fn sample_execution_transaction() -> Transaction<CurrentNetwork> {
        static INSTANCE: OnceCell<Transaction<CurrentNetwork>> = OnceCell::new();
        INSTANCE
            .get_or_init(|| {
                // Initialize a new program.
                let program = sample_program();
                // Add the program.
                VM::add_program(&program).unwrap();

                // Initialize the RNG.
                let rng = &mut test_crypto_rng();
                // Initialize a new caller.
                let caller_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
                let address = Address::try_from(&caller_private_key).unwrap();
                // Authorize.
                let authorization = VM::authorize(
                    &caller_private_key,
                    program.id(),
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
                let (_response, transaction) = VM::execute(authorization, rng).unwrap();
                // Verify.
                assert!(VM::verify(&transaction));
                // Return the transaction.
                transaction
            })
            .clone()
    }

    pub(crate) fn sample_transition() -> Transition<CurrentNetwork> {
        // Retrieve the transaction.
        let transaction = sample_execution_transaction();
        // Retrieve the transitions.
        let mut transitions = transaction.transitions();
        // Return a transition.
        transitions.next().cloned().unwrap()
    }
}
