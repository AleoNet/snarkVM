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

use super::*;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum FinalizeMode {
    /// Invoke finalize as a real run.
    RealRun,
    /// Invoke finalize as a dry run.
    DryRun,
}

impl FinalizeMode {
    /// Returns the u8 value of the finalize mode.
    #[inline]
    pub const fn to_u8(self) -> u8 {
        match self {
            Self::RealRun => 0,
            Self::DryRun => 1,
        }
    }

    /// Returns a finalize mode from a given u8.
    #[inline]
    pub fn from_u8(value: u8) -> Result<Self> {
        match value {
            0 => Ok(Self::RealRun),
            1 => Ok(Self::DryRun),
            _ => bail!("Invalid finalize mode of '{value}'"),
        }
    }
}

impl<N: Network, C: ConsensusStorage<N>> VM<N, C> {
    /// Finalizes the given transactions into the VM,
    /// returning the list of accepted transaction IDs, rejected transaction IDs, and finalize operations.
    #[inline]
    pub fn finalize<'a, const FINALIZE_MODE: u8>(
        &self,
        transactions: impl Iterator<Item = &'a Transaction<N>> + ExactSizeIterator,
    ) -> Result<(Vec<N::TransactionID>, Vec<N::TransactionID>, Vec<FinalizeOperation<N>>)> {
        let timer = timer!("VM::finalize");

        // Retrieve the number of transactions.
        let num_transactions = transactions.len();
        // Determine the finalize mode.
        let finalize_mode = FinalizeMode::from_u8(FINALIZE_MODE)?;

        // Perform the finalize operation on the preset finalize mode.
        atomic_finalize!(self.finalize_store(), finalize_mode, {
            // Acquire the write lock on the process.
            // Note: Due to the highly-sensitive nature of processing all `finalize` calls,
            // we choose to acquire the write lock for the entire duration of this atomic batch.
            let mut process = self.process.write();

            // Initialize a list of the accepted transactions.
            let mut accepted = Vec::with_capacity(num_transactions);
            // Initialize a list of the rejected transactions.
            let mut rejected = Vec::with_capacity(num_transactions);
            // Initialize a list of the fees from rejected transactions.
            let mut rejected_fees = Vec::with_capacity(num_transactions);
            // Initialize a list for the finalize operations.
            let mut finalize_operations = Vec::new();
            // Initialize a list for the deployed stacks.
            let mut stacks = Vec::new();

            // Finalize the transactions.
            for transaction in transactions {
                // Process the transaction in an isolated atomic batch.
                // - If the transaction succeeds, the finalize operations are stored.
                // - If the transaction fails, the atomic batch is aborted and no finalize operations are stored.
                let outcome = match transaction {
                    // The finalize operation here involves appending the 'stack',
                    // and adding the program to the finalize tree.
                    Transaction::Deploy(_, _, deployment, _) => {
                        process.finalize_deployment(self.finalize_store(), deployment).map(|(stack, operations)| {
                            // Store the stack, if this is a real run.
                            if finalize_mode == FinalizeMode::RealRun {
                                stacks.push(stack);
                            }
                            // Return the finalize operations.
                            Some(operations)
                        })
                    }
                    // The finalize operation here involves calling 'update_key_value',
                    // and update the respective leaves of the finalize tree.
                    Transaction::Execute(_, execution, _) => {
                        process.finalize_execution(self.finalize_store(), execution).map(Some)
                    }
                    // There are no finalize operations here.
                    Transaction::Fee(..) => Ok(None),
                };
                lap!(timer, "Finalizing transaction {}", transaction.id());

                match outcome {
                    // If the transaction succeeded to finalize, continue to the next transaction.
                    Ok(operations) => {
                        // Store the finalize operations.
                        if let Some(operations) = operations {
                            finalize_operations.extend(operations);
                        }
                        // Store the transaction in the accepted list.
                        accepted.push(transaction.id());
                    }
                    // If the transaction failed to finalize, abort and continue to the next transaction.
                    Err(error) => {
                        warn!("Rejected transaction '{}': (in finalize) {error}", transaction.id());
                        // Store the transaction ID in the rejected list.
                        rejected.push(transaction.id());
                        // Store the fee in the rejected fee list.
                        match transaction {
                            Transaction::Deploy(_, _, _, fee) => rejected_fees.push(fee),
                            Transaction::Execute(_, _, Some(fee)) => rejected_fees.push(fee),
                            // This is a foundational bug - the caller is violating protocol rules.
                            // Note: This will abort the entire atomic batch.
                            Transaction::Execute(_, _, None) => return Err("Rejected execute transaction has no fee"),
                            // This is a foundational bug - the caller is violating protocol rules.
                            // Note: This will abort the entire atomic batch.
                            Transaction::Fee(..) => return Err("Fee transactions cannot be rejected"),
                        }
                        // Rewind the atomic batch to the previous transaction and continue to the next transaction.
                        continue;
                    }
                }
            }

            // TODO (howardwu): Check that the fee transaction corresponds to a rejected transaction.
            // // Ensure that all rejected transactions have a corresponding 'Transaction::Fee' type
            // // in the accepted transactions, with the same fee transition.
            // for reject in rejected.iter() {
            //     accepted.contains(reject);
            // }

            // Ensure all transactions were processed.
            if accepted.len() != num_transactions {
                // Note: This will abort the entire atomic batch.
                return Err("Not all transactions were processed in 'VM::finalize'");
            }

            /* Start the commit process. */

            // Commit all of the stacks to the process.
            if !stacks.is_empty() {
                stacks.into_iter().for_each(|stack| process.add_stack(stack))
            }

            finish!(timer); // <- Note: This timer does **not** include the time to write batch to DB.

            // Handles the atomic batch, based on the 'finalize_mode'.
            // If this is a real run, 'atomic_finalize!' will commit the atomic batch.
            // If this is a dry run, 'atomic_finalize!' will abort the atomic batch.
            Ok((accepted, rejected, finalize_operations))
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        store::helpers::memory::ConsensusMemory,
        vm::test_helpers,
        Block,
        Header,
        Metadata,
        Program,
        Transaction,
        Transactions,
        Transition,
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
        let program_name = format!("a{}.aleo", Alphanumeric.sample_string(rng, 8));

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

    get.or_init account[r0] 0u64 into r2;
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

    get.or_init account[r0] 0u64 into r3;
    get.or_init account[r1] 0u64 into r4;

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
        let transaction = Transaction::deploy(vm, private_key, &program, additional_fee, None, rng)?;

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
        let transactions = Transactions::from(transactions);
        // Construct the metadata associated with the block.
        let metadata = Metadata::new(
            CurrentNetwork::ID,
            previous_block.round() + 1,
            previous_block.height() + 1,
            CurrentNetwork::STARTING_SUPPLY,
            0,
            CurrentNetwork::GENESIS_COINBASE_TARGET,
            CurrentNetwork::GENESIS_PROOF_TARGET,
            previous_block.last_coinbase_target(),
            previous_block.last_coinbase_timestamp(),
            CurrentNetwork::GENESIS_TIMESTAMP + 1,
        )?;

        let header = Header::from(
            *vm.block_store().current_state_root(),
            transactions.to_root().unwrap(),
            Field::zero(),
            Field::zero(),
            metadata,
        )?;

        let block = Block::new(private_key, previous_block.hash(), header, transactions, None, rng)?;

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

            // Prepare the inputs.
            let inputs =
                [Value::<CurrentNetwork>::Record(record), Value::<CurrentNetwork>::from_str("100u64").unwrap()]
                    .into_iter();

            // Execute.
            let transaction =
                Transaction::execute(vm, private_key, ("credits.aleo", "split"), inputs, None, None, rng).unwrap();

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
        let transaction = Transaction::execute(
            vm,
            &caller_private_key,
            (program_id, function_name),
            inputs.into_iter(),
            Some(additional_fee),
            None,
            rng,
        )
        .unwrap();
        // Verify.
        assert!(vm.verify_transaction(&transaction));

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

    #[test]
    fn test_finalize_duplicate_deployment() {
        let rng = &mut TestRng::default();

        let vm = crate::vm::test_helpers::sample_vm();

        // Fetch a deployment transaction.
        let deployment_transaction = crate::vm::test_helpers::sample_deployment_transaction(rng);

        // Finalize the transaction.
        let (accepted_transactions, rejected_transactions, _) =
            vm.finalize::<{ FinalizeMode::RealRun.to_u8() }>([deployment_transaction.clone()].iter()).unwrap();
        assert_eq!(accepted_transactions, vec![deployment_transaction.id()]);
        assert!(rejected_transactions.is_empty());

        // Ensure the VM can't redeploy the same transaction.
        let (accepted_transactions, rejected_transactions, _) =
            vm.finalize::<{ FinalizeMode::RealRun.to_u8() }>([deployment_transaction.clone()].iter()).unwrap();
        assert!(accepted_transactions.is_empty());
        assert_eq!(rejected_transactions, vec![deployment_transaction.id()]);

        // Ensure the dry run of the redeployment will also fail.
        let (accepted_transactions, rejected_transactions, _) =
            vm.finalize::<{ FinalizeMode::DryRun.to_u8() }>([deployment_transaction.clone()].iter()).unwrap();
        assert!(accepted_transactions.is_empty());
        assert_eq!(rejected_transactions, vec![deployment_transaction.id()]);
    }

    #[test]
    fn test_finalize_many() {
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
            let (accepted_transactions, rejected_transactions, _) =
                vm.finalize::<{ FinalizeMode::DryRun.to_u8() }>(transactions.iter()).unwrap();

            // Assert that the accepted and rejected transactions are correct.
            assert_eq!(accepted_transactions, vec![mint_10.id(), transfer_10.id(), transfer_20.id()]);
            assert!(rejected_transactions.is_empty());
        }

        // Starting Balance = 20
        // Transfer_20 -> Balance = 20 - 20 = 0
        // Mint_10 -> Balance = 0 + 10 = 10
        // Mint_20 -> Balance = 10 + 20 = 30
        // Transfer_30 -> Balance = 30 - 30 = 0
        {
            let transactions = [transfer_20.clone(), mint_10.clone(), mint_20.clone(), transfer_30.clone()];
            let (accepted_transactions, rejected_transactions, _) =
                vm.finalize::<{ FinalizeMode::DryRun.to_u8() }>(transactions.iter()).unwrap();

            // Assert that the accepted and rejected transactions are correct.
            assert_eq!(accepted_transactions, vec![transfer_20.id(), mint_10.id(), mint_20.id(), transfer_30.id()]);
            assert!(rejected_transactions.is_empty());
        }

        // Starting Balance = 20
        // Transfer_20 -> Balance = 20 - 20 = 0
        // Transfer_10 -> Balance = 0 - 10 = -10 (should be rejected)
        {
            let transactions = [transfer_20.clone(), transfer_10.clone()];
            let (accepted_transactions, rejected_transactions, _) =
                vm.finalize::<{ FinalizeMode::DryRun.to_u8() }>(transactions.iter()).unwrap();

            // Assert that the accepted and rejected transactions are correct.
            assert_eq!(accepted_transactions, vec![transfer_20.id()]);
            assert_eq!(rejected_transactions, vec![transfer_10.id()]);
        }

        // Starting Balance = 20
        // Mint_20 -> Balance = 20 + 20
        // Transfer_30 -> Balance = 40 - 30 = 10
        // Transfer_20 -> Balance = 10 - 20 = -10 (should be rejected)
        // Transfer_10 -> Balance = 10 - 10 = 0
        {
            let transactions = [mint_20.clone(), transfer_30.clone(), transfer_20.clone(), transfer_10.clone()];
            let (accepted_transactions, rejected_transactions, _) =
                vm.finalize::<{ FinalizeMode::DryRun.to_u8() }>(transactions.iter()).unwrap();

            // Assert that the accepted and rejected transactions are correct.
            assert_eq!(accepted_transactions, vec![mint_20.id(), transfer_30.id(), transfer_10.id()]);
            assert_eq!(rejected_transactions, vec![transfer_20.id()]);
        }
    }
}
