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

use super::*;

impl<N: Network, C: ConsensusStorage<N>> VM<N, C> {
    /// Returns `true` if the transaction is valid.
    pub fn verify_transaction(&self, transaction: &Transaction<N>, rejected_id: Option<Field<N>>) -> bool {
        match self.check_transaction(transaction, rejected_id) {
            Ok(_) => true,
            Err(error) => {
                warn!("{error}");
                false
            }
        }
    }

    /// Returns `true` if the deployment is valid.
    pub fn verify_deployment(&self, deployment: &Deployment<N>) -> bool {
        match self.check_deployment(deployment) {
            Ok(_) => true,
            Err(error) => {
                warn!("{error}");
                false
            }
        }
    }

    /// Returns `true` if the execution is valid.
    pub fn verify_execution(&self, execution: &Execution<N>) -> bool {
        match self.check_execution(execution) {
            Ok(_) => true,
            Err(error) => {
                warn!("{error}");
                false
            }
        }
    }

    /// Returns `true` if the fee is valid.
    pub fn verify_fee(&self, fee: &Fee<N>, deployment_or_execution_id: Field<N>) -> bool {
        match self.check_fee(fee, deployment_or_execution_id) {
            Ok(_) => true,
            Err(error) => {
                warn!("{error}");
                false
            }
        }
    }

    /// Verifies the transaction in the VM. On failure, returns an error.
    #[inline]
    pub fn check_transaction(&self, transaction: &Transaction<N>, rejected_id: Option<Field<N>>) -> Result<()> {
        let timer = timer!("VM::verify");

        // Compute the Merkle root of the transaction.
        match transaction.to_root() {
            // Ensure the transaction ID is correct.
            Ok(root) => {
                if *transaction.id() != root {
                    bail!("Incorrect transaction ID ({})", transaction.id());
                }
            }
            Err(error) => {
                bail!("Failed to compute the Merkle root of the transaction: {error}\n{transaction}");
            }
        };
        lap!(timer, "Verify the transaction id");

        // Ensure there are no duplicate transition IDs.
        if has_duplicates(transaction.transition_ids()) {
            bail!("Found duplicate transition in the transaction");
        }

        /* Input */

        // Ensure there are no duplicate input IDs.
        if has_duplicates(transaction.input_ids()) {
            bail!("Found duplicate input IDs in the transaction");
        }

        // Ensure there are no duplicate serial numbers.
        if has_duplicates(transaction.serial_numbers()) {
            bail!("Found duplicate serial numbers in the transaction");
        }

        // Ensure there are no duplicate tags.
        if has_duplicates(transaction.tags()) {
            bail!("Found duplicate tags in the transaction");
        }

        /* Output */

        // Ensure there are no duplicate output IDs.
        if has_duplicates(transaction.output_ids()) {
            bail!("Found duplicate output IDs in the transaction");
        }

        // Ensure there are no duplicate commitments.
        if has_duplicates(transaction.commitments()) {
            bail!("Found duplicate commitments in the transaction");
        }

        // Ensure there are no duplicate nonces.
        if has_duplicates(transaction.nonces()) {
            bail!("Found duplicate nonces in the transaction");
        }

        /* Metadata */

        // Ensure there are no duplicate transition public keys.
        if has_duplicates(transaction.transition_public_keys()) {
            bail!("Found duplicate transition public keys in the transaction");
        }

        // Ensure there are no duplicate transition commitments.
        if has_duplicates(transaction.transition_commitments()) {
            bail!("Found duplicate transition commitments in the transaction");
        }

        lap!(timer, "Check for duplicate elements");

        match transaction {
            Transaction::Deploy(id, owner, deployment, fee) => {
                // Ensure the rejected ID is not present.
                ensure!(rejected_id.is_none(), "Transaction should not have a rejected ID (deployment)");
                // Compute the deployment ID.
                let Ok(deployment_id) = deployment.to_deployment_id() else {
                    bail!("Failed to compute the Merkle root for deployment transaction '{id}'")
                };
                // Verify the signature corresponds to the transaction ID.
                ensure!(owner.verify(deployment_id), "Invalid owner signature for deployment transaction '{id}'");
                // Verify the fee.
                self.check_fee(fee, deployment_id)?;
                // Verify the deployment.
                self.check_deployment(deployment)?;
            }
            Transaction::Execute(id, execution, fee) => {
                // Ensure the rejected ID is not present.
                ensure!(rejected_id.is_none(), "Transaction should not have a rejected ID (execution)");
                // Compute the execution ID.
                let Ok(execution_id) = execution.to_execution_id() else {
                    bail!("Failed to compute the Merkle root for execution transaction '{id}'")
                };
                // TODO (raychu86): Remove `is_split` check once batch executions are supported.
                // Ensure the fee is present, if the transaction is not a mint or split.
                if !((transaction.is_mint() || transaction.is_split()) && execution.len() == 1) && fee.is_none() {
                    bail!("Transaction is missing a fee (execution)");
                }
                // Verify the fee.
                if let Some(fee) = fee {
                    self.check_fee(fee, execution_id)?;
                }
                // Verify the execution.
                self.check_execution(execution)?;
            }
            Transaction::Fee(_, fee) => {
                // Ensure the fee is nonzero.
                ensure!(!fee.is_zero()?, "Invalid fee (zero)");
                // Retrieve the rejected ID.
                let Some(rejected_id) = rejected_id else {
                    bail!("Transaction is missing a rejected ID (fee)");
                };
                // Verify the fee.
                self.check_fee(fee, rejected_id)?;
            }
        };

        lap!(timer, "Verify the transaction");

        finish!(timer);

        Ok(())
    }

    /// Verifies the given deployment. On failure, returns an error.
    #[inline]
    fn check_deployment(&self, deployment: &Deployment<N>) -> Result<()> {
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
                Ok(())
            }
            Err(error) => {
                finish!(timer);
                bail!("Deployment verification failed: {error}");
            }
        }
    }

    /// Verifies the given execution. On failure, returns an error.
    #[inline]
    fn check_execution(&self, execution: &Execution<N>) -> Result<()> {
        let timer = timer!("VM::verify_execution");

        // Verify the execution.
        let verification = self.process.read().verify_execution(execution);
        finish!(timer);

        match verification {
            // Ensure the global state root exists in the block store.
            Ok(()) => match self.block_store().contains_state_root(&execution.global_state_root()) {
                Ok(true) => Ok(()),
                Ok(false) => bail!("Execution verification failed: global state root not found"),
                Err(error) => bail!("Execution verification failed: {error}"),
            },
            Err(error) => bail!("Execution verification failed: {error}"),
        }
    }

    /// Verifies the given fee. On failure, returns an error.
    #[inline]
    fn check_fee(&self, fee: &Fee<N>, deployment_or_execution_id: Field<N>) -> Result<()> {
        let timer = timer!("VM::verify_fee");

        // Ensure the fee does not exceed the limit.
        ensure!(*fee.amount()? < N::MAX_FEE, "Fee verification failed: fee exceeds the maximum limit");

        // Verify the fee.
        let verification = self.process.read().verify_fee(fee, deployment_or_execution_id);
        finish!(timer);

        match verification {
            // Ensure the global state root exists in the block store.
            Ok(()) => match self.block_store().contains_state_root(&fee.global_state_root()) {
                Ok(true) => Ok(()),
                Ok(false) => bail!("Fee verification failed: global state root not found"),
                Err(error) => bail!("Fee verification failed: {error}"),
            },
            Err(error) => bail!("Fee verification failed: {error}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::vm::test_helpers::sample_finalize_state;
    use console::{
        account::{Address, ViewKey},
        types::Field,
    };
    use ledger_block::{Block, Header, Metadata, Transaction};

    type CurrentNetwork = test_helpers::CurrentNetwork;

    #[test]
    fn test_verify() {
        let rng = &mut TestRng::default();
        let vm = crate::vm::test_helpers::sample_vm_with_genesis_block(rng);

        // Fetch a deployment transaction.
        let deployment_transaction = crate::vm::test_helpers::sample_deployment_transaction(rng);
        // Ensure the transaction verifies.
        assert!(vm.check_transaction(&deployment_transaction, None).is_ok());
        assert!(vm.verify_transaction(&deployment_transaction, None));

        // Fetch an execution transaction.
        let execution_transaction = crate::vm::test_helpers::sample_execution_transaction_with_fee(rng);
        // Ensure the transaction verifies.
        assert!(vm.check_transaction(&execution_transaction, None).is_ok());
        assert!(vm.verify_transaction(&execution_transaction, None));
    }

    #[test]
    fn test_verify_deployment() {
        let rng = &mut TestRng::default();
        let vm = crate::vm::test_helpers::sample_vm();

        // Fetch the program from the deployment.
        let program = crate::vm::test_helpers::sample_program();

        // Deploy the program.
        let deployment = vm.deploy_raw(&program, rng).unwrap();

        // Ensure the deployment is valid.
        assert!(vm.check_deployment(&deployment).is_ok());
        assert!(vm.verify_deployment(&deployment));

        // Ensure that deserialization doesn't break the transaction verification.
        let serialized_deployment = deployment.to_string();
        let deployment_transaction: Deployment<CurrentNetwork> = serde_json::from_str(&serialized_deployment).unwrap();
        assert!(vm.check_deployment(&deployment_transaction).is_ok());
        assert!(vm.verify_deployment(&deployment_transaction));
    }

    #[test]
    fn test_verify_execution() {
        let rng = &mut TestRng::default();
        let vm = crate::vm::test_helpers::sample_vm_with_genesis_block(rng);

        // Fetch a execution transaction.
        let transaction = crate::vm::test_helpers::sample_execution_transaction_with_fee(rng);

        match transaction {
            Transaction::Execute(_, execution, _) => {
                // Ensure the proof exists.
                assert!(execution.proof().is_some());
                // Verify the execution.
                assert!(vm.check_execution(&execution).is_ok());
                assert!(vm.verify_execution(&execution));

                // Ensure that deserialization doesn't break the transaction verification.
                let serialized_execution = execution.to_string();
                let recovered_execution: Execution<CurrentNetwork> =
                    serde_json::from_str(&serialized_execution).unwrap();
                assert!(vm.check_execution(&recovered_execution).is_ok());
                assert!(vm.verify_execution(&recovered_execution));
            }
            _ => panic!("Expected an execution transaction"),
        }
    }

    #[test]
    fn test_verify_fee() {
        let rng = &mut TestRng::default();
        let vm = crate::vm::test_helpers::sample_vm_with_genesis_block(rng);

        // Fetch a execution transaction.
        let transaction = crate::vm::test_helpers::sample_execution_transaction_with_fee(rng);

        match transaction {
            Transaction::Execute(_, execution, Some(fee)) => {
                let execution_id = execution.to_execution_id().unwrap();

                // Ensure the proof exists.
                assert!(fee.proof().is_some());
                // Verify the fee.
                assert!(vm.check_fee(&fee, execution_id).is_ok());
                assert!(vm.verify_fee(&fee, execution_id));

                // Ensure that deserialization doesn't break the transaction verification.
                let serialized_fee = fee.to_string();
                let recovered_fee: Fee<CurrentNetwork> = serde_json::from_str(&serialized_fee).unwrap();
                assert!(vm.check_fee(&recovered_fee, execution_id).is_ok());
                assert!(vm.verify_fee(&recovered_fee, execution_id));
            }
            _ => panic!("Expected an execution with a fee"),
        }
    }

    #[test]
    fn test_check_transaction_execution() -> Result<()> {
        let rng = &mut TestRng::default();

        // Initialize the VM.
        let vm = crate::vm::test_helpers::sample_vm();
        // Initialize the genesis block.
        let genesis = crate::vm::test_helpers::sample_genesis_block(rng);
        // Update the VM.
        vm.add_next_block(&genesis).unwrap();

        // Fetch a valid execution transaction.
        let valid_transaction = crate::vm::test_helpers::sample_execution_transaction_with_fee(rng);
        assert!(vm.check_transaction(&valid_transaction, None).is_ok());
        assert!(vm.verify_transaction(&valid_transaction, None));

        // Fetch an invalid execution transaction.
        let invalid_transaction = crate::vm::test_helpers::sample_execution_transaction_without_fee(rng);
        assert!(vm.check_transaction(&invalid_transaction, None).is_err());
        assert!(!vm.verify_transaction(&invalid_transaction, None));

        Ok(())
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

        // Prepare the fee.
        let credits = records.values().next().unwrap().decrypt(&caller_view_key).unwrap();
        let fee = (credits, 10);

        // Initialize the VM.
        let vm = crate::vm::test_helpers::sample_vm();
        // Update the VM.
        vm.add_next_block(&genesis).unwrap();

        // Deploy.
        let program = crate::vm::test_helpers::sample_program();
        let deployment_transaction = vm.deploy(&caller_private_key, &program, fee, None, rng).unwrap();

        // Construct the new block header.
        let transactions = vm.speculate(sample_finalize_state(1), [deployment_transaction].iter()).unwrap();

        // Construct the metadata associated with the block.
        let deployment_metadata = Metadata::new(
            CurrentNetwork::ID,
            1,
            1,
            CurrentNetwork::STARTING_SUPPLY,
            0,
            0,
            CurrentNetwork::GENESIS_COINBASE_TARGET,
            CurrentNetwork::GENESIS_PROOF_TARGET,
            genesis.last_coinbase_target(),
            genesis.last_coinbase_timestamp(),
            CurrentNetwork::GENESIS_TIMESTAMP + 1,
        )
        .unwrap();

        let deployment_header = Header::from(
            *vm.block_store().current_state_root(),
            transactions.to_transactions_root().unwrap(),
            transactions.to_finalize_root().unwrap(),
            crate::vm::test_helpers::sample_ratifications_root(),
            Field::zero(),
            deployment_metadata,
        )
        .unwrap();

        // Construct a new block for the deploy transaction.
        let deployment_block =
            Block::new_beacon(&caller_private_key, genesis.hash(), deployment_header, transactions, vec![], None, rng)
                .unwrap();

        // Add the deployment block.
        vm.add_next_block(&deployment_block).unwrap();

        // Fetch the unspent records.
        let records = deployment_block.records().collect::<indexmap::IndexMap<_, _>>();

        // Prepare the inputs.
        let inputs = [
            Value::<CurrentNetwork>::from_str(&address.to_string()).unwrap(),
            Value::<CurrentNetwork>::from_str("10u64").unwrap(),
        ]
        .into_iter();

        // Prepare the fee.
        let credits = records.values().next().unwrap().decrypt(&caller_view_key).unwrap();
        let fee_in_microcredits = 10;
        let fee = Some((credits, fee_in_microcredits));

        // Execute.
        let transaction = vm.execute(&caller_private_key, ("testing.aleo", "mint"), inputs, fee, None, rng).unwrap();

        // Verify.
        assert!(vm.check_transaction(&transaction, None).is_ok());
        assert!(vm.verify_transaction(&transaction, None));
    }

    #[test]
    fn test_failed_credits_deployment() {
        let rng = &mut TestRng::default();
        let vm = crate::vm::test_helpers::sample_vm();

        // Fetch the credits program
        let program = Program::credits().unwrap();

        // Ensure that the program can't be deployed.
        assert!(vm.deploy_raw(&program, rng).is_err());

        // Create a new `credits.aleo` program.
        let program = Program::from_str(
            r"
program credits.aleo;

record token:
    owner as address.private;
    amount as u64.private;

function compute:
    input r0 as u32.private;
    add r0 r0 into r1;
    output r1 as u32.public;",
        )
        .unwrap();

        // Ensure that the program can't be deployed.
        assert!(vm.deploy_raw(&program, rng).is_err());
    }
}
