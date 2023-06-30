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
use crate::{ConfirmedTransaction, Rejected, Transactions};

impl<N: Network, C: ConsensusStorage<N>> VM<N, C> {
    /// Speculates on the given list of transactions in the VM, returning the confirmed transactions.
    #[inline]
    pub fn speculate<'a>(
        &self,
        state: FinalizeGlobalState,
        transactions: impl ExactSizeIterator<Item = &'a Transaction<N>>,
    ) -> Result<Transactions<N>> {
        let timer = timer!("VM::speculate");

        // Performs a **dry-run** over the list of transactions.
        let confirmed_transactions = self.atomic_speculate(state, transactions)?;

        finish!(timer, "Finished dry-run of the transactions");

        // Return the transactions.
        Ok(confirmed_transactions.into_iter().collect())
    }

    /// Finalizes the given transactions into the VM.
    #[inline]
    pub fn finalize(&self, state: FinalizeGlobalState, transactions: &Transactions<N>) -> Result<()> {
        let timer = timer!("VM::finalize");

        // Performs a **real-run** of finalize over the list of transactions.
        self.atomic_finalize(state, transactions)?;

        finish!(timer, "Finished real-run of finalize");
        Ok(())
    }
}

impl<N: Network, C: ConsensusStorage<N>> VM<N, C> {
    /// Performs atomic speculation over a list of transactions, and returns the confirmed transactions.
    #[inline]
    #[rustfmt::skip]
    fn atomic_speculate<'a>(
        &self,
        state: FinalizeGlobalState,
        transactions: impl ExactSizeIterator<Item = &'a Transaction<N>>,
    ) -> Result<Vec<ConfirmedTransaction<N>>> {
        let timer = timer!("VM::atomic_speculate");

        // Retrieve the number of transactions.
        let num_transactions = transactions.len();

        // Perform the finalize operation on the preset finalize mode.
        atomic_finalize!(self.finalize_store(), FinalizeMode::DryRun, {
            // Acquire the write lock on the process.
            // Note: Due to the highly-sensitive nature of processing all `finalize` calls,
            // we choose to acquire the write lock for the entire duration of this atomic batch.
            let process = self.process.write();

            // Retrieve the finalize store.
            let store = self.finalize_store();

            // Initialize a list of the confirmed transactions.
            let mut confirmed = Vec::with_capacity(num_transactions);

            // Finalize the transactions.
            for (index, transaction) in transactions.enumerate() {
                // Convert the transaction index to a u32.
                // Note: On failure, this will abort the entire atomic batch.
                let index = u32::try_from(index).map_err(|_| "Failed to convert transaction index".to_string())?;

                // Process the transaction in an isolated atomic batch.
                // - If the transaction succeeds, the finalize operations are stored.
                // - If the transaction fails, the atomic batch is aborted and no finalize operations are stored.
                let outcome = match transaction {
                    // The finalize operation here involves appending the 'stack',
                    // and adding the program to the finalize tree.
                    Transaction::Deploy(_, program_owner, deployment, fee) => match process.finalize_deployment(store, deployment) {
                        // Construct the accepted deploy transaction.
                        Ok((_, finalize)) => ConfirmedTransaction::accepted_deploy(index, transaction.clone(), finalize).map_err(|e| e.to_string()),
                        // Construct the rejected deploy transaction.
                        Err(_error) => {
                            // Construct the fee transaction.
                            // Note: On failure, this will abort the entire atomic batch.
                            let fee_tx = Transaction::from_fee(fee.clone()).map_err(|e| e.to_string())?;
                            // Construct the rejected deployment.
                            let rejected = Rejected::new_deployment(*program_owner, *deployment.clone());
                            // Construct the rejected deploy transaction.
                            ConfirmedTransaction::rejected_deploy(index, fee_tx, rejected).map_err(|e| e.to_string())
                        }
                    }
                    // The finalize operation here involves calling 'update_key_value',
                    // and update the respective leaves of the finalize tree.
                    Transaction::Execute(_, execution, fee) => match process.finalize_execution(state, store, execution) {
                        // Construct the accepted execute transaction.
                        Ok(finalize) => ConfirmedTransaction::accepted_execute(index, transaction.clone(), finalize).map_err(|e| e.to_string()),
                        // Construct the rejected execute transaction.
                        Err(_error) => match fee {
                            Some(fee) => {
                                // Construct the fee transaction.
                                // Note: On failure, this will abort the entire atomic batch.
                                let fee_tx = Transaction::from_fee(fee.clone()).map_err(|e| e.to_string())?;
                                // Construct the rejected execution.
                                let rejected = Rejected::new_execution(execution.clone());
                                // Construct the rejected execute transaction.
                                ConfirmedTransaction::rejected_execute(index, fee_tx, rejected).map_err(|e| e.to_string())
                            },
                            // This is a foundational bug - the caller is violating protocol rules.
                            // Note: This will abort the entire atomic batch.
                            None => Err("Rejected execute transaction has no fee".to_string()),
                        },
                    }
                    // There are no finalize operations here.
                    // Note: This will abort the entire atomic batch.
                    Transaction::Fee(..) => Err("Cannot speculate on a fee transaction".to_string()),
                };
                lap!(timer, "Speculated on transaction '{}'", transaction.id());

                match outcome {
                    // If the transaction succeeded, store it and continue to the next transaction.
                    Ok(confirmed_transaction) => confirmed.push(confirmed_transaction),
                    // If the transaction failed, abort the entire batch.
                    Err(error) => {
                        eprintln!("Critical bug in speculate: {error}\n\n{transaction}");
                        // Note: This will abort the entire atomic batch.
                        return Err(format!("Failed to speculate on transaction - {error}"));
                    }
                }
            }

            // Ensure all transactions were processed.
            if confirmed.len() != num_transactions {
                // Note: This will abort the entire atomic batch.
                return Err("Not all transactions were processed in 'VM::atomic_speculate'".to_string());
            }

            finish!(timer);

            // On return, 'atomic_finalize!' will abort the batch, and return the confirmed transactions.
            Ok(confirmed)
        })
    }

    /// Performs atomic finalization over a list of transactions.
    #[inline]
    fn atomic_finalize(&self, state: FinalizeGlobalState, transactions: &Transactions<N>) -> Result<()> {
        let timer = timer!("VM::atomic_finalize");

        // Perform the finalize operation on the preset finalize mode.
        atomic_finalize!(self.finalize_store(), FinalizeMode::RealRun, {
            // Acquire the write lock on the process.
            // Note: Due to the highly-sensitive nature of processing all `finalize` calls,
            // we choose to acquire the write lock for the entire duration of this atomic batch.
            let mut process = self.process.write();

            // Retrieve the finalize store.
            let store = self.finalize_store();

            // Initialize a list for the deployed stacks.
            let mut stacks = Vec::new();

            // Finalize the transactions.
            for (index, transaction) in transactions.iter().enumerate() {
                // Convert the transaction index to a u32.
                // Note: On failure, this will abort the entire atomic batch.
                let index = u32::try_from(index).map_err(|_| "Failed to convert transaction index".to_string())?;

                // Process the transaction in an isolated atomic batch.
                // - If the transaction succeeds, the finalize operations are stored.
                // - If the transaction fails, the atomic batch is aborted and no finalize operations are stored.
                let outcome: Result<(), String> = match transaction {
                    ConfirmedTransaction::AcceptedDeploy(idx, transaction, finalize) => {
                        // Ensure the index matches the expected index.
                        if index != *idx {
                            // Note: This will abort the entire atomic batch.
                            return Err("Mismatch in accepted deploy transaction index".to_string());
                        }
                        // Extract the deployment from the transaction.
                        let deployment = match transaction {
                            Transaction::Deploy(_, _, deployment, _) => deployment,
                            // Note: This will abort the entire atomic batch.
                            _ => return Err("Expected deploy transaction".to_string()),
                        };
                        // The finalize operation here involves appending the 'stack',
                        // and adding the program to the finalize tree.
                        match process.finalize_deployment(store, deployment) {
                            // Ensure the finalize operations match the expected.
                            Ok((stack, finalize_operations)) => match finalize == &finalize_operations {
                                // Store the stack.
                                true => stacks.push(stack),
                                // Note: This will abort the entire atomic batch.
                                false => {
                                    return Err("Mismatch in finalize operations for an accepted deploy".to_string());
                                }
                            },
                            // Note: This will abort the entire atomic batch.
                            Err(error) => {
                                return Err(format!("Failed to finalize an accepted deploy transaction - {error}"));
                            }
                        };
                        Ok(())
                    }
                    ConfirmedTransaction::AcceptedExecute(idx, transaction, finalize) => {
                        // Ensure the index matches the expected index.
                        if index != *idx {
                            // Note: This will abort the entire atomic batch.
                            return Err("Mismatch in accepted execute transaction index".to_string());
                        }
                        // Extract the execution from the transaction.
                        let execution = match transaction {
                            Transaction::Execute(_, execution, _) => execution,
                            // Note: This will abort the entire atomic batch.
                            _ => return Err("Expected execute transaction".to_string()),
                        };
                        // The finalize operation here involves calling 'update_key_value',
                        // and update the respective leaves of the finalize tree.
                        match process.finalize_execution(state, store, execution) {
                            // Ensure the finalize operations match the expected.
                            Ok(finalize_operations) => {
                                if finalize != &finalize_operations {
                                    // Note: This will abort the entire atomic batch.
                                    return Err("Mismatch in finalize operations for an accepted execute".to_string());
                                }
                            }
                            // Note: This will abort the entire atomic batch.
                            Err(error) => {
                                return Err(format!("Failed to finalize an accepted execute transaction - {error}"));
                            }
                        }
                        Ok(())
                    }
                    ConfirmedTransaction::RejectedDeploy(idx, _fee_transaction, rejected) => {
                        // Ensure the index matches the expected index.
                        if index != *idx {
                            // Note: This will abort the entire atomic batch.
                            return Err("Mismatch in rejected deploy transaction index".to_string());
                        }
                        // Extract the rejected deployment.
                        let Some(deployment) = rejected.deployment() else {
                            // Note: This will abort the entire atomic batch.
                            return Err("Expected rejected deployment".to_string());
                        };
                        // TODO (howardwu): Ensure this fee corresponds to the deployment.
                        // Attempt to finalize the deployment, which should fail.
                        #[cfg(debug_assertions)]
                        if let Ok(..) = process.finalize_deployment(store, deployment) {
                            // Note: This will abort the entire atomic batch.
                            return Err("Failed to reject a rejected deploy transaction".to_string());
                        }
                        Ok(())
                    }
                    ConfirmedTransaction::RejectedExecute(idx, _fee_transaction, rejected) => {
                        // Ensure the index matches the expected index.
                        if index != *idx {
                            // Note: This will abort the entire atomic batch.
                            return Err("Mismatch in rejected execute transaction index".to_string());
                        }
                        // Extract the rejected execution.
                        let Some(execution) = rejected.execution() else {
                            // Note: This will abort the entire atomic batch.
                            return Err("Expected rejected execution".to_string());
                        };
                        // TODO (howardwu): Ensure this fee corresponds to the execution.
                        // Attempt to finalize the execution, which should fail.
                        #[cfg(debug_assertions)]
                        if let Ok(..) = process.finalize_execution(state, store, execution) {
                            // Note: This will abort the entire atomic batch.
                            return Err("Failed to reject a rejected execute transaction".to_string());
                        }
                        Ok(())
                    }
                };
                lap!(timer, "Finalizing transaction {}", transaction.id());

                match outcome {
                    // If the transaction succeeded to finalize, continue to the next transaction.
                    Ok(()) => (),
                    // If the transaction failed to finalize, abort and continue to the next transaction.
                    Err(error) => {
                        eprintln!("Critical bug in finalize: {error}\n\n{transaction}");
                        // Note: This will abort the entire atomic batch.
                        return Err(format!("Failed to finalize on transaction - {error}"));
                    }
                }
            }

            /* Start the commit process. */

            // Commit all of the stacks to the process.
            if !stacks.is_empty() {
                stacks.into_iter().for_each(|stack| process.add_stack(stack))
            }

            finish!(timer); // <- Note: This timer does **not** include the time to write batch to DB.

            Ok(())
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        block::{Block, Header, Metadata, Transaction, Transition},
        program::Program,
        store::helpers::memory::ConsensusMemory,
        vm::{test_helpers, test_helpers::sample_finalize_state},
    };
    use console::{
        account::{Address, PrivateKey, ViewKey},
        program::{Ciphertext, Record},
        types::Field,
    };

    use rand::distributions::DistString;

    type CurrentNetwork = test_helpers::CurrentNetwork;

    /// Sample a new program and deploy it to the VM. Returns the program name.
    fn new_program_deployment<R: Rng + CryptoRng>(
        vm: &VM<CurrentNetwork, ConsensusMemory<CurrentNetwork>>,
        private_key: &PrivateKey<CurrentNetwork>,
        previous_block: &Block<CurrentNetwork>,
        unspent_records: &mut Vec<Record<CurrentNetwork, Ciphertext<CurrentNetwork>>>,
        rng: &mut R,
    ) -> Result<(String, Block<CurrentNetwork>)> {
        let program_name = format!("a{}.aleo", Alphanumeric.sample_string(rng, 8).to_lowercase());

        let program = Program::<CurrentNetwork>::from_str(&format!(
            "
program {program_name};

mapping account:
    // The token owner.
    key owner as address.public;
    // The token amount.
    value amount as u64.public;

function mint_public:
    input r0 as address.public;
    input r1 as u64.public;
    finalize r0 r1;

finalize mint_public:
    input r0 as address.public;
    input r1 as u64.public;

    get.or_use account[r0] 0u64 into r2;
    add r2 r1 into r3;
    set r3 into account[r0];

function transfer_public:
    input r0 as address.public;
    input r1 as u64.public;

    finalize self.caller r0 r1;

finalize transfer_public:
    input r0 as address.public;
    input r1 as address.public;
    input r2 as u64.public;

    get.or_use account[r0] 0u64 into r3;
    get.or_use account[r1] 0u64 into r4;

    sub r3 r2 into r5;
    add r4 r2 into r6;

    set r5 into account[r0];
    set r6 into account[r1];"
        ))?;

        // Prepare the additional fee.
        let view_key = ViewKey::<CurrentNetwork>::try_from(private_key)?;
        let credits = unspent_records.pop().unwrap().decrypt(&view_key)?;
        let additional_fee = (credits, 10);

        // Deploy.
        let transaction = vm.deploy(private_key, &program, additional_fee, None, rng)?;

        // Construct the new block.
        let next_block = sample_next_block(vm, private_key, &[transaction], previous_block, unspent_records, rng)?;

        Ok((program_name, next_block))
    }

    /// Construct a new block based on the given transactions.
    fn sample_next_block<R: Rng + CryptoRng>(
        vm: &VM<CurrentNetwork, ConsensusMemory<CurrentNetwork>>,
        private_key: &PrivateKey<CurrentNetwork>,
        transactions: &[Transaction<CurrentNetwork>],
        previous_block: &Block<CurrentNetwork>,
        unspent_records: &mut Vec<Record<CurrentNetwork, Ciphertext<CurrentNetwork>>>,
        rng: &mut R,
    ) -> Result<Block<CurrentNetwork>> {
        // Construct the new block header.
        let transactions = vm.speculate(sample_finalize_state(1), transactions.iter())?;
        // Construct the metadata associated with the block.
        let metadata = Metadata::new(
            CurrentNetwork::ID,
            previous_block.round() + 1,
            previous_block.height() + 1,
            CurrentNetwork::STARTING_SUPPLY,
            0,
            0,
            CurrentNetwork::GENESIS_COINBASE_TARGET,
            CurrentNetwork::GENESIS_PROOF_TARGET,
            previous_block.last_coinbase_target(),
            previous_block.last_coinbase_timestamp(),
            CurrentNetwork::GENESIS_TIMESTAMP + 1,
        )?;

        let header = Header::from(
            *vm.block_store().current_state_root(),
            transactions.to_transactions_root().unwrap(),
            transactions.to_finalize_root().unwrap(),
            crate::vm::test_helpers::sample_ratifications_root(),
            Field::zero(),
            metadata,
        )?;

        let block = Block::new(private_key, previous_block.hash(), header, transactions, vec![], None, rng)?;

        // Track the new records.
        let new_records = block
            .transitions()
            .cloned()
            .flat_map(Transition::into_records)
            .map(|(_, record)| record)
            .collect::<Vec<_>>();
        unspent_records.extend(new_records);

        Ok(block)
    }

    /// Generate split transactions for the unspent records.
    fn generate_splits<R: Rng + CryptoRng>(
        vm: &VM<CurrentNetwork, ConsensusMemory<CurrentNetwork>>,
        private_key: &PrivateKey<CurrentNetwork>,
        previous_block: &Block<CurrentNetwork>,
        unspent_records: &mut Vec<Record<CurrentNetwork, Ciphertext<CurrentNetwork>>>,
        rng: &mut R,
    ) -> Result<Block<CurrentNetwork>> {
        // Prepare the additional fee.
        let view_key = ViewKey::<CurrentNetwork>::try_from(private_key)?;

        // Generate split transactions.
        let mut transactions = Vec::new();
        while !unspent_records.is_empty() {
            let record = unspent_records.pop().unwrap().decrypt(&view_key)?;

            // Fetch the record balance and divide it in half.
            let split_balance = match record.find(&[Identifier::from_str("microcredits")?]) {
                Ok(Entry::Private(Plaintext::Literal(Literal::U64(amount), _))) => *amount / 2,
                _ => bail!("fee record does not contain a microcredits entry"),
            };

            // Prepare the inputs.
            let inputs = [
                Value::<CurrentNetwork>::Record(record),
                Value::<CurrentNetwork>::from_str(&format!("{split_balance}u64")).unwrap(),
            ]
            .into_iter();

            // Execute.
            let transaction = vm.execute(private_key, ("credits.aleo", "split"), inputs, None, None, rng).unwrap();

            transactions.push(transaction);
        }

        // Construct the new block.
        sample_next_block(vm, private_key, &transactions, previous_block, unspent_records, rng)
    }

    /// Create an execution transaction.
    fn create_execution(
        vm: &VM<CurrentNetwork, ConsensusMemory<CurrentNetwork>>,
        caller_private_key: PrivateKey<CurrentNetwork>,
        program_id: &str,
        function_name: &str,
        inputs: Vec<Value<CurrentNetwork>>,
        unspent_records: &mut Vec<Record<CurrentNetwork, Ciphertext<CurrentNetwork>>>,
        rng: &mut TestRng,
    ) -> Transaction<CurrentNetwork> {
        assert!(vm.contains_program(&ProgramID::from_str(program_id).unwrap()));

        // Prepare the additional fee.
        let view_key = ViewKey::<CurrentNetwork>::try_from(caller_private_key).unwrap();
        let credits = unspent_records.pop().unwrap().decrypt(&view_key).unwrap();
        let additional_fee = (credits, 1);

        // Execute.
        let transaction = vm
            .execute(
                &caller_private_key,
                (program_id, function_name),
                inputs.into_iter(),
                Some(additional_fee),
                None,
                rng,
            )
            .unwrap();
        // Verify.
        assert!(vm.verify_transaction(&transaction, None));

        // Return the transaction.
        transaction
    }

    /// Sample a public mint transaction.
    fn sample_mint_public(
        vm: &VM<CurrentNetwork, ConsensusMemory<CurrentNetwork>>,
        caller_private_key: PrivateKey<CurrentNetwork>,
        program_id: &str,
        recipient: Address<CurrentNetwork>,
        amount: u64,
        unspent_records: &mut Vec<Record<CurrentNetwork, Ciphertext<CurrentNetwork>>>,
        rng: &mut TestRng,
    ) -> Transaction<CurrentNetwork> {
        let inputs = vec![
            Value::<CurrentNetwork>::from_str(&recipient.to_string()).unwrap(),
            Value::<CurrentNetwork>::from_str(&format!("{amount}u64")).unwrap(),
        ];

        create_execution(vm, caller_private_key, program_id, "mint_public", inputs, unspent_records, rng)
    }

    /// Sample a public transfer transaction.
    fn sample_transfer_public(
        vm: &VM<CurrentNetwork, ConsensusMemory<CurrentNetwork>>,
        caller_private_key: PrivateKey<CurrentNetwork>,
        program_id: &str,
        recipient: Address<CurrentNetwork>,
        amount: u64,
        unspent_records: &mut Vec<Record<CurrentNetwork, Ciphertext<CurrentNetwork>>>,
        rng: &mut TestRng,
    ) -> Transaction<CurrentNetwork> {
        let inputs = vec![
            Value::<CurrentNetwork>::from_str(&recipient.to_string()).unwrap(),
            Value::<CurrentNetwork>::from_str(&format!("{amount}u64")).unwrap(),
        ];

        create_execution(vm, caller_private_key, program_id, "transfer_public", inputs, unspent_records, rng)
    }

    /// A helper method to construct the rejected transaction format for `atomic_finalize`.
    fn reject(index: u32, transaction: &Transaction<CurrentNetwork>) -> ConfirmedTransaction<CurrentNetwork> {
        match transaction {
            Transaction::Execute(_, execution, fee) => ConfirmedTransaction::RejectedExecute(
                index,
                Transaction::from_fee(fee.clone().unwrap()).unwrap(),
                Rejected::new_execution(execution.clone()),
            ),
            _ => panic!("only reject execution transactions"),
        }
    }

    #[test]
    fn test_finalize_duplicate_deployment() {
        let rng = &mut TestRng::default();

        let vm = crate::vm::test_helpers::sample_vm();

        // Fetch a deployment transaction.
        let deployment_transaction = crate::vm::test_helpers::sample_deployment_transaction(rng);

        // Construct the program name.
        let program_id = ProgramID::from_str("testing.aleo").unwrap();

        // Prepare the confirmed transactions.
        let confirmed_transactions =
            vm.speculate(sample_finalize_state(1), [deployment_transaction.clone()].iter()).unwrap();

        // Ensure the VM does not contain this program.
        assert!(!vm.contains_program(&program_id));

        // Finalize the transaction.
        assert!(vm.finalize(sample_finalize_state(1), &confirmed_transactions).is_ok());

        // Ensure the VM contains this program.
        assert!(vm.contains_program(&program_id));

        // Ensure the VM can't redeploy the same transaction.
        assert!(vm.finalize(sample_finalize_state(1), &confirmed_transactions).is_err());

        // Ensure the VM contains this program.
        assert!(vm.contains_program(&program_id));

        // Ensure the dry run of the redeployment will cause a reject transaction to be created.
        let candidate_transactions =
            vm.atomic_speculate(sample_finalize_state(1), [deployment_transaction].iter()).unwrap();
        assert_eq!(candidate_transactions.len(), 1);
        assert!(matches!(candidate_transactions[0], ConfirmedTransaction::RejectedDeploy(..)));
    }

    #[test]
    fn test_atomic_finalize_many() {
        let rng = &mut TestRng::default();

        // Sample a private key and address for the caller.
        let caller_private_key = test_helpers::sample_genesis_private_key(rng);
        let caller_address = Address::try_from(&caller_private_key).unwrap();

        // Sample a private key and address for the recipient.
        let recipient_private_key = PrivateKey::new(rng).unwrap();
        let recipient_address = Address::try_from(&recipient_private_key).unwrap();

        // Initialize the vm.
        let vm = test_helpers::sample_vm_with_genesis_block(rng);

        // Deploy a new program.
        let genesis =
            vm.block_store().get_block(&vm.block_store().get_block_hash(0).unwrap().unwrap()).unwrap().unwrap();

        // Get the unspent records.
        let mut unspent_records = genesis
            .transitions()
            .cloned()
            .flat_map(Transition::into_records)
            .map(|(_, record)| record)
            .collect::<Vec<_>>();

        // Construct the deployment block.
        let (program_id, deployment_block) =
            new_program_deployment(&vm, &caller_private_key, &genesis, &mut unspent_records, rng).unwrap();

        // Add the deployment block to the VM.
        vm.add_next_block(&deployment_block).unwrap();

        // Generate more records to use for the next block.
        let splits_block =
            generate_splits(&vm, &caller_private_key, &deployment_block, &mut unspent_records, rng).unwrap();

        // Add the splits block to the VM.
        vm.add_next_block(&splits_block).unwrap();

        // Construct the initial mint.
        let initial_mint =
            sample_mint_public(&vm, caller_private_key, &program_id, caller_address, 20, &mut unspent_records, rng);
        let initial_mint_block =
            sample_next_block(&vm, &caller_private_key, &[initial_mint], &splits_block, &mut unspent_records, rng)
                .unwrap();

        // Add the block to the vm.
        vm.add_next_block(&initial_mint_block).unwrap();

        // Construct a mint and a transfer.
        let mint_10 =
            sample_mint_public(&vm, caller_private_key, &program_id, caller_address, 10, &mut unspent_records, rng);
        let mint_20 =
            sample_mint_public(&vm, caller_private_key, &program_id, caller_address, 20, &mut unspent_records, rng);
        let transfer_10 = sample_transfer_public(
            &vm,
            caller_private_key,
            &program_id,
            recipient_address,
            10,
            &mut unspent_records,
            rng,
        );
        let transfer_20 = sample_transfer_public(
            &vm,
            caller_private_key,
            &program_id,
            recipient_address,
            20,
            &mut unspent_records,
            rng,
        );
        let transfer_30 = sample_transfer_public(
            &vm,
            caller_private_key,
            &program_id,
            recipient_address,
            30,
            &mut unspent_records,
            rng,
        );

        // TODO (raychu86): Confirm that the finalize_operations here are correct.

        // Starting Balance = 20
        // Mint_10 -> Balance = 20 + 10  = 30
        // Transfer_10 -> Balance = 30 - 10 = 20
        // Transfer_20 -> Balance = 20 - 20 = 0
        {
            let transactions = [mint_10.clone(), transfer_10.clone(), transfer_20.clone()];
            let confirmed_transactions = vm.atomic_speculate(sample_finalize_state(1), transactions.iter()).unwrap();

            // Assert that all the transactions are accepted.
            assert_eq!(confirmed_transactions.len(), 3);
            confirmed_transactions.iter().for_each(|confirmed_tx| assert!(confirmed_tx.is_accepted()));

            assert_eq!(confirmed_transactions[0].transaction(), &mint_10);
            assert_eq!(confirmed_transactions[1].transaction(), &transfer_10);
            assert_eq!(confirmed_transactions[2].transaction(), &transfer_20);
        }

        // Starting Balance = 20
        // Transfer_20 -> Balance = 20 - 20 = 0
        // Mint_10 -> Balance = 0 + 10 = 10
        // Mint_20 -> Balance = 10 + 20 = 30
        // Transfer_30 -> Balance = 30 - 30 = 0
        {
            let transactions = [transfer_20.clone(), mint_10.clone(), mint_20.clone(), transfer_30.clone()];
            let confirmed_transactions = vm.atomic_speculate(sample_finalize_state(1), transactions.iter()).unwrap();

            // Assert that all the transactions are accepted.
            assert_eq!(confirmed_transactions.len(), 4);
            confirmed_transactions.iter().for_each(|confirmed_tx| assert!(confirmed_tx.is_accepted()));

            // Ensure that the transactions are in the correct order.
            assert_eq!(confirmed_transactions[0].transaction(), &transfer_20);
            assert_eq!(confirmed_transactions[1].transaction(), &mint_10);
            assert_eq!(confirmed_transactions[2].transaction(), &mint_20);
            assert_eq!(confirmed_transactions[3].transaction(), &transfer_30);
        }

        // Starting Balance = 20
        // Transfer_20 -> Balance = 20 - 20 = 0
        // Transfer_10 -> Balance = 0 - 10 = -10 (should be rejected)
        {
            let transactions = [transfer_20.clone(), transfer_10.clone()];
            let confirmed_transactions = vm.atomic_speculate(sample_finalize_state(1), transactions.iter()).unwrap();

            // Assert that the accepted and rejected transactions are correct.
            assert_eq!(confirmed_transactions.len(), 2);

            assert!(confirmed_transactions[0].is_accepted());
            assert!(confirmed_transactions[1].is_rejected());

            assert_eq!(confirmed_transactions[0].transaction(), &transfer_20);
            assert_eq!(confirmed_transactions[1], reject(1, &transfer_10));
        }

        // Starting Balance = 20
        // Mint_20 -> Balance = 20 + 20
        // Transfer_30 -> Balance = 40 - 30 = 10
        // Transfer_20 -> Balance = 10 - 20 = -10 (should be rejected)
        // Transfer_10 -> Balance = 10 - 10 = 0
        {
            let transactions = [mint_20.clone(), transfer_30.clone(), transfer_20.clone(), transfer_10.clone()];
            let confirmed_transactions = vm.atomic_speculate(sample_finalize_state(1), transactions.iter()).unwrap();

            // Assert that the accepted and rejected transactions are correct.
            assert_eq!(confirmed_transactions.len(), 4);

            assert!(confirmed_transactions[0].is_accepted());
            assert!(confirmed_transactions[1].is_accepted());
            assert!(confirmed_transactions[2].is_rejected());
            assert!(confirmed_transactions[3].is_accepted());

            assert_eq!(confirmed_transactions[0].transaction(), &mint_20);
            assert_eq!(confirmed_transactions[1].transaction(), &transfer_30);
            assert_eq!(confirmed_transactions[2], reject(2, &transfer_20));
            assert_eq!(confirmed_transactions[3].transaction(), &transfer_10);
        }
    }

    #[test]
    fn test_finalize_catch_halt() {
        let rng = &mut TestRng::default();

        // Sample a private key, view key, and address for the caller.
        let caller_private_key = test_helpers::sample_genesis_private_key(rng);
        let caller_view_key = ViewKey::try_from(&caller_private_key).unwrap();

        for finalize_logic in &[
            "finalize ped_hash:
    input r0 as u128.public;
    hash.ped64 r0 into r1 as field;
    set r1 into hashes[r0];",
            "finalize ped_hash:
    input r0 as u128.public;
    div r0 0u128 into r1;",
        ] {
            // Initialize the vm.
            let vm = test_helpers::sample_vm_with_genesis_block(rng);

            // Deploy a new program.
            let genesis =
                vm.block_store().get_block(&vm.block_store().get_block_hash(0).unwrap().unwrap()).unwrap().unwrap();

            // Get the unspent records.
            let mut unspent_records = genesis
                .transitions()
                .cloned()
                .flat_map(Transition::into_records)
                .map(|(_, record)| record)
                .collect::<Vec<_>>();

            // Create a program that will always cause a E::halt in the finalize execution.
            let program_id = "testing.aleo";
            let program = Program::<CurrentNetwork>::from_str(&format!(
                "
program {program_id};

mapping hashes:
    key preimage as u128.public;
    value val as field.public;

function ped_hash:
    input r0 as u128.public;
    // hash.ped64 r0 into r1 as field; // <--- This will cause a E::halt.
    finalize r0;

{finalize_logic}"
            ))
            .unwrap();

            let credits = unspent_records.pop().unwrap().decrypt(&caller_view_key).unwrap();
            let additional_fee = (credits, 10);

            // Deploy the program.
            let deployment_transaction = vm.deploy(&caller_private_key, &program, additional_fee, None, rng).unwrap();

            // Construct the deployment block.
            let deployment_block = sample_next_block(
                &vm,
                &caller_private_key,
                &[deployment_transaction],
                &genesis,
                &mut unspent_records,
                rng,
            )
            .unwrap();

            // Add the deployment block to the VM.
            vm.add_next_block(&deployment_block).unwrap();

            // Construct a transaction that will cause a E::halt in the finalize execution.
            let inputs = vec![Value::<CurrentNetwork>::from_str("1u128").unwrap()];
            let transaction =
                create_execution(&vm, caller_private_key, program_id, "ped_hash", inputs, &mut unspent_records, rng);

            // Speculatively execute the transaction. Ensure that this call does not panic and returns a rejected transaction.
            let confirmed_transactions = vm.speculate(sample_finalize_state(1), [transaction.clone()].iter()).unwrap();

            // Ensure that the transaction is rejected.
            assert_eq!(confirmed_transactions.len(), 1);
            assert!(transaction.is_execute());
            if let Transaction::Execute(_, execution, fee) = transaction {
                let fee_transaction = Transaction::from_fee(fee.unwrap()).unwrap();
                let expected_confirmed_transaction =
                    ConfirmedTransaction::RejectedExecute(0, fee_transaction, Rejected::new_execution(execution));

                let confirmed_transaction = confirmed_transactions.iter().next().unwrap();
                assert_eq!(confirmed_transaction, &expected_confirmed_transaction);
            }
        }
    }

    #[test]
    fn test_rejected_transaction_should_not_update_storage() {
        let rng = &mut TestRng::default();

        // Sample a private key.
        let private_key = test_helpers::sample_genesis_private_key(rng);
        let address = Address::try_from(&private_key).unwrap();

        // Initialize the vm.
        let vm = test_helpers::sample_vm_with_genesis_block(rng);

        // Deploy a new program.
        let genesis =
            vm.block_store().get_block(&vm.block_store().get_block_hash(0).unwrap().unwrap()).unwrap().unwrap();

        // Get the unspent records.
        let mut unspent_records = genesis
            .transitions()
            .cloned()
            .flat_map(Transition::into_records)
            .map(|(_, record)| record)
            .collect::<Vec<_>>();

        // Generate more records to use for the next block.
        let splits_block = generate_splits(&vm, &private_key, &genesis, &mut unspent_records, rng).unwrap();

        // Add the splits block to the VM.
        vm.add_next_block(&splits_block).unwrap();

        // Construct the deployment block.
        let deployment_block = {
            let program = Program::<CurrentNetwork>::from_str(
                "
program testing.aleo;

mapping entries:
    key owner as address.public;
    value data as u8.public;

function compute:
    input r0 as u8.public;
    finalize self.caller r0;

finalize compute:
    input r0 as address.public;
    input r1 as u8.public;
    get.or_use entries[r0] r1 into r2;
    add r1 r2 into r3;
    set r3 into entries[r0];
    get entries[r0] into r4;
    add r4 r1 into r5;
    set r5 into entries[r0];
",
            )
            .unwrap();

            // Prepare the additional fee.
            let view_key = ViewKey::<CurrentNetwork>::try_from(private_key).unwrap();
            let credits = unspent_records.pop().unwrap().decrypt(&view_key).unwrap();
            let additional_fee = (credits, 10);

            // Deploy.
            let transaction = vm.deploy(&private_key, &program, additional_fee, None, rng).unwrap();

            // Construct the new block.
            sample_next_block(&vm, &private_key, &[transaction], &splits_block, &mut unspent_records, rng).unwrap()
        };

        // Add the deployment block to the VM.
        vm.add_next_block(&deployment_block).unwrap();

        // Generate more records to use for the next block.
        let splits_block = generate_splits(&vm, &private_key, &deployment_block, &mut unspent_records, rng).unwrap();

        // Add the splits block to the VM.
        vm.add_next_block(&splits_block).unwrap();

        // Create an execution transaction, that will be rejected.
        let r0 = Value::<CurrentNetwork>::from_str("100u8").unwrap();
        let first = create_execution(&vm, private_key, "testing.aleo", "compute", vec![r0], &mut unspent_records, rng);

        // Construct the next block.
        let next_block =
            sample_next_block(&vm, &private_key, &[first], &splits_block, &mut unspent_records, rng).unwrap();

        // Check that the transaction was rejected.
        assert!(next_block.transactions().iter().next().unwrap().is_rejected());

        // Add the next block to the VM.
        vm.add_next_block(&next_block).unwrap();

        // Check that the storage was not updated.
        let program_id = ProgramID::from_str("testing.aleo").unwrap();
        let mapping_name = Identifier::from_str("entries").unwrap();
        let value = vm
            .finalize_store()
            .get_value_speculative(&program_id, &mapping_name, &Plaintext::from(Literal::Address(address)))
            .unwrap();
        println!("{:?}", value);
        assert!(
            !vm.finalize_store()
                .contains_key_confirmed(&program_id, &mapping_name, &Plaintext::from(Literal::Address(address)))
                .unwrap()
        );

        // Create an execution transaction, that will be rejected.
        let r0 = Value::<CurrentNetwork>::from_str("100u8").unwrap();
        let first = create_execution(&vm, private_key, "testing.aleo", "compute", vec![r0], &mut unspent_records, rng);

        // Create an execution transaction, that will be accepted.
        let r0 = Value::<CurrentNetwork>::from_str("1u8").unwrap();
        let second = create_execution(&vm, private_key, "testing.aleo", "compute", vec![r0], &mut unspent_records, rng);

        // Construct the next block.
        let next_block =
            sample_next_block(&vm, &private_key, &[first, second], &next_block, &mut unspent_records, rng).unwrap();

        // Check that the first transaction was rejected.
        assert!(next_block.transactions().iter().next().unwrap().is_rejected());

        // Add the next block to the VM.
        vm.add_next_block(&next_block).unwrap();

        // Check that the storage was updated correctly.
        let value = vm
            .finalize_store()
            .get_value_speculative(&program_id, &mapping_name, &Plaintext::from(Literal::Address(address)))
            .unwrap()
            .unwrap();
        let expected = Value::<CurrentNetwork>::from_str("3u8").unwrap();
        assert_eq!(value, expected);
    }
}
