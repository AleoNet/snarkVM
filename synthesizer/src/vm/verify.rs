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

use super::*;

impl<N: Network, C: ConsensusStorage<N>> VM<N, C> {
    /// Verifies the transaction in the VM.
    #[inline]
    pub fn verify(&self, transaction: &Transaction<N>) -> bool {
        let timer = timer!("VM::verify");

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
        lap!(timer, "Verify the transaction id");

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
        lap!(timer, "Check for duplicate elements");

        let verification = match transaction {
            Transaction::Deploy(_, deployment, fee) => {
                // Check the deployment size.
                if let Err(error) = Transaction::check_deployment_size(deployment) {
                    warn!("Invalid transaction size (deployment): {error}");
                    return false;
                }
                // Verify the deployment.
                self.verify_deployment(deployment)
                    // Verify the fee.
                    && self.verify_fee(fee)
            }
            Transaction::Execute(_, execution, additional_fee) => {
                // Check the deployment size.
                if let Err(error) = Transaction::check_execution_size(execution) {
                    warn!("Invalid transaction size (execution): {error}");
                    return false;
                }

                // Verify the additional fee, if it exists.
                let check_additional_fee = match additional_fee {
                    Some(additional_fee) => self.verify_fee(additional_fee),
                    None => true,
                };

                // Verify the execution.
                self.verify_execution(execution)
                    // Verify the additional fee.
                    && check_additional_fee
            }
        };

        lap!(timer, "Verify the transaction");

        finish!(timer);

        verification
    }

    /// Verifies the given deployment.
    #[inline]
    fn verify_deployment(&self, deployment: &Deployment<N>) -> bool {
        let timer = timer!("VM::verify_deployment");

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
            Ok(()) => {
                finish!(timer);
                true
            }
            Err(error) => {
                warn!("Deployment verification failed: {error}");
                finish!(timer);
                false
            }
        }
    }

    /// Verifies the given execution.
    #[inline]
    fn verify_execution(&self, execution: &Execution<N>) -> bool {
        let timer = timer!("VM::verify_execution");

        // Verify the execution.
        let verification = self.process.read().verify_execution::<true>(execution);
        finish!(timer);

        match verification {
            // Ensure the global state root exists in the block store.
            Ok(()) => match self.block_store().contains_state_root(&execution.global_state_root()) {
                Ok(true) => true,
                Ok(false) => {
                    warn!("Execution verification failed: global state root not found");
                    false
                }
                Err(error) => {
                    warn!("Execution verification failed: {error}");
                    false
                }
            },
            Err(error) => {
                warn!("Execution verification failed: {error}");
                false
            }
        }
    }

    /// Verifies the given fee.
    #[inline]
    fn verify_fee(&self, fee: &Fee<N>) -> bool {
        let timer = timer!("VM::verify_fee");

        // Verify the fee.
        let verification = self.process.read().verify_fee(fee);
        finish!(timer);

        match verification {
            // Ensure the global state root exists in the block store.
            Ok(()) => match self.block_store().contains_state_root(&fee.global_state_root()) {
                Ok(true) => true,
                Ok(false) => {
                    warn!("Fee verification failed: global state root not found");
                    false
                }
                Err(error) => {
                    warn!("Fee verification failed: {error}");
                    false
                }
            },
            Err(error) => {
                warn!("Fee verification failed: {error}");
                false
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::{Block, Header, Inclusion, Metadata, Transaction, Transactions};
    use console::{
        account::{Address, ViewKey},
        types::Field,
    };

    type CurrentNetwork = test_helpers::CurrentNetwork;

    #[test]
    fn test_verify() {
        let rng = &mut TestRng::default();
        let vm = crate::vm::test_helpers::sample_vm_with_genesis_block(rng);

        // Fetch a deployment transaction.
        let deployment_transaction = crate::vm::test_helpers::sample_deployment_transaction(rng);
        // Ensure the transaction verifies.
        assert!(vm.verify(&deployment_transaction));

        // Fetch an execution transaction.
        let execution_transaction = crate::vm::test_helpers::sample_execution_transaction(rng);
        // Ensure the transaction verifies.
        assert!(vm.verify(&execution_transaction));
    }

    #[test]
    fn test_verify_deployment() {
        let rng = &mut TestRng::default();
        let vm = crate::vm::test_helpers::sample_vm();

        // Fetch the program from the deployment.
        let program = crate::vm::test_helpers::sample_program();

        // Deploy the program.
        let deployment = vm.deploy(&program, rng).unwrap();

        // Ensure the deployment is valid.
        assert!(vm.verify_deployment(&deployment));
    }

    #[test]
    fn test_verify_execution() {
        let rng = &mut TestRng::default();
        let vm = crate::vm::test_helpers::sample_vm_with_genesis_block(rng);

        // Fetch a execution transaction.
        let transaction = crate::vm::test_helpers::sample_execution_transaction(rng);

        match transaction {
            Transaction::Execute(_, execution, _) => {
                // Ensure the inclusion proof exists.
                assert!(execution.inclusion_proof().is_some());
                // Verify the inclusion.
                assert!(Inclusion::verify_execution(&execution).is_ok());
                // Verify the execution.
                assert!(vm.verify_execution(&execution));
            }
            _ => panic!("Expected an execution transaction"),
        }
    }

    #[test]
    fn test_verify_deploy_and_execute() {
        // Initialize the RNG.
        let rng = &mut TestRng::default();

        // Initialize a new caller.
        let caller_private_key = crate::vm::test_helpers::sample_genesis_private_key(rng);
        let caller_view_key = ViewKey::try_from(&caller_private_key).unwrap();
        let address = Address::try_from(&caller_private_key).unwrap();

        // Initialize the genesis block.
        let genesis = crate::vm::test_helpers::sample_genesis_block(rng);

        // Fetch the unspent records.
        let records = genesis.records().collect::<indexmap::IndexMap<_, _>>();

        // Prepare the additional fee.
        let credits = records.values().next().unwrap().decrypt(&caller_view_key).unwrap();
        let additional_fee = (credits, 10);

        // Initialize the VM.
        let vm = crate::vm::test_helpers::sample_vm();
        // Update the VM.
        vm.add_next_block(&genesis).unwrap();

        // Deploy.
        let program = crate::vm::test_helpers::sample_program();
        let deployment_transaction =
            Transaction::deploy(&vm, &caller_private_key, &program, additional_fee, None, rng).unwrap();

        // Construct the new block header.
        let transactions = Transactions::from(&[deployment_transaction]);
        // Construct the metadata associated with the block.
        let deployment_metadata = Metadata::new(
            CurrentNetwork::ID,
            1,
            1,
            CurrentNetwork::GENESIS_COINBASE_TARGET,
            CurrentNetwork::GENESIS_PROOF_TARGET,
            genesis.last_coinbase_target(),
            genesis.last_coinbase_timestamp(),
            CurrentNetwork::GENESIS_TIMESTAMP + 1,
        )
        .unwrap();

        let deployment_header = Header::from(
            *vm.block_store().current_state_root(),
            transactions.to_root().unwrap(),
            Field::zero(),
            deployment_metadata,
        )
        .unwrap();

        // Construct a new block for the deploy transaction.
        let deployment_block =
            Block::new(&caller_private_key, genesis.hash(), deployment_header, transactions, None, rng).unwrap();

        // Add the deployment block.
        vm.add_next_block(&deployment_block).unwrap();

        // Authorize.
        let authorization = vm
            .authorize(
                &caller_private_key,
                "testing.aleo",
                "mint",
                [
                    Value::<CurrentNetwork>::from_str(&address.to_string()).unwrap(),
                    Value::<CurrentNetwork>::from_str("10u64").unwrap(),
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
    }
}
