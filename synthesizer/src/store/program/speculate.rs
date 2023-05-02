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

use crate::{
    process::{Deployment, Execution, FinalizeRegisters, Load, Store},
    program::finalize::Command,
    store::{ConsensusStorage, FinalizeTree, MerkleTreeUpdate},
    Transaction,
    VM,
};
use console::{
    network::prelude::*,
    program::{Identifier, Plaintext, ProgramID, Value},
    types::Field,
};

use indexmap::{IndexMap, IndexSet};

// TODO (raychu86): Move this out of `store/program`

/// The speculative executor for the program state.
#[derive(Clone)]
pub struct Speculate<N: Network> {
    /// The latest finalize root.
    /// This is used to ensure that the speculate state is building off the same state.
    pub latest_finalize_root: Field<N>,

    /// The list of accepted transactions that have been processed.
    pub accepted_transactions: Vec<N::TransactionID>,
    /// The list of transactions that have been processed. Including ones that have been rejected.
    pub processed_transactions: Vec<N::TransactionID>,

    /// The values updated in the speculate state. (`program ID`, (`mapping name`, (`key`, `value`)))
    pub speculate_state: IndexMap<ProgramID<N>, IndexMap<Identifier<N>, IndexMap<Vec<u8>, Value<N>>>>,

    /// The operations being performed.
    pub operations: IndexMap<N::TransactionID, Vec<(ProgramID<N>, MerkleTreeUpdate<N>)>>,
}

impl<N: Network> Speculate<N> {
    /// Initializes a new instance of `Speculate`.
    pub fn new(latest_finalize_root: Field<N>) -> Self {
        Self {
            latest_finalize_root,
            accepted_transactions: Default::default(),
            processed_transactions: Default::default(),

            speculate_state: Default::default(),
            operations: Default::default(),
        }
    }

    /// Returns `true` if the transaction has been processed.
    pub fn contains_transaction(&self, transaction_id: &N::TransactionID) -> bool {
        self.accepted_transactions.contains(transaction_id)
            || self.processed_transactions.contains(transaction_id)
            || self.operations.contains_key(transaction_id)
    }

    /// Returns the accepted transactions.
    pub fn accepted_transactions(&self) -> &[N::TransactionID] {
        &self.accepted_transactions
    }

    /// Returns the processed transactions.
    pub fn processed_transactions(&self) -> &[N::TransactionID] {
        &self.processed_transactions
    }

    pub fn operations(&self) -> &IndexMap<N::TransactionID, Vec<(ProgramID<N>, MerkleTreeUpdate<N>)>> {
        &self.operations
    }

    /// Returns the speculative value for the given `program ID`, `mapping name`, and `key`.
    pub fn get_value(
        &self,
        program_id: &ProgramID<N>,
        mapping_name: &Identifier<N>,
        key: &Plaintext<N>,
    ) -> Result<Option<Value<N>>> {
        // Get the list of mappings associated with the program.
        let mappings = match self.speculate_state.get(program_id) {
            Some(mappings) => mappings,
            None => return Ok(None),
        };

        // Get the mapping associated with the mapping name.
        let mapping = match mappings.get(mapping_name) {
            Some(mapping) => mapping,
            None => return Ok(None),
        };

        // Get the value associated with the key.
        Ok(mapping.get(&key.to_bytes_le()?).cloned())
    }

    /// Stores the given `(key, value)` pair at the given `program ID` and `mapping name` in speculative storage.
    /// If the `key` does not exist, the `(key, value)` pair is initialized.
    /// If the `key` already exists, the `value` is overwritten.
    pub fn update_key_value(
        &mut self,
        program_id: &ProgramID<N>,
        mapping_name: &Identifier<N>,
        key: Plaintext<N>,
        value: Value<N>,
    ) -> Result<()> {
        // Get the list of mappings associated with the program.
        let mappings = self.speculate_state.entry(*program_id).or_insert(IndexMap::new());

        // Get the mapping associated with the mapping name.
        let mapping = mappings.entry(*mapping_name).or_insert(IndexMap::new());

        // Update the key-value pair.
        mapping.insert(key.to_bytes_le()?, value);

        Ok(())
    }

    /// Speculatively execute the given deployment.
    fn speculate_deployment<C: ConsensusStorage<N>>(
        &mut self,
        vm: &VM<N, C>,
        transaction_id: N::TransactionID,
        deployment: &Deployment<N>,
    ) -> Result<()> {
        // Fetch the program data.
        let program = deployment.program();
        let program_id = program.id();

        // Ensure that the program has not already been deployed.
        if vm.contains_program(program_id) {
            bail!("The program has already been deployed");
        }

        // Compute the mapping IDs.
        let mapping_ids = program
            .mappings()
            .values()
            .map(|mapping| N::hash_bhp1024(&(program_id, mapping.name()).to_bits_le()))
            .collect::<Result<IndexSet<_>>>()?;

        // Determine the operations that are being executed.
        let mut operations = Vec::with_capacity(mapping_ids.len());

        // Iterate through the mapping IDs.
        for mapping_id in mapping_ids.iter() {
            // Log the Merkle tree operation.
            operations.push((*program_id, MerkleTreeUpdate::InsertMapping(*mapping_id)));
        }

        // Update the log of operations.
        if !operations.is_empty() {
            self.operations.insert(transaction_id, operations);
        }

        Ok(())
    }

    /// Speculatively execute the given execution.
    fn speculate_execution<C: ConsensusStorage<N>>(
        &mut self,
        vm: &VM<N, C>,
        transaction_id: N::TransactionID,
        execution: &Execution<N>,
    ) -> Result<()> {
        // Fetch the process from the VM.
        let process_lock = vm.process();
        let process = process_lock.read();

        // Specify the mapping ids that are updated by the transaction.
        let mut updated_mapping_ids = IndexSet::new();

        // Determine the operations that are being executed.
        let mut operations = Vec::new();

        // Process the transitions, starting from the last one.
        for transition in execution.transitions().rev() {
            // Retrieve the program ID.
            let program_id = transition.program_id();
            // Retrieve the stack.
            let stack = process.get_stack(program_id)?;
            // Retrieve the function name.
            let function_name = transition.function_name();

            // If there is a finalize scope, perform the speculative finalize.
            if let Some((_, finalize)) = stack.get_function(function_name)?.finalize() {
                // Retrieve the finalize inputs.
                let inputs = match transition.finalize() {
                    Some(inputs) => inputs,
                    // Ensure the transition contains finalize inputs.
                    None => bail!("The transition is missing inputs for 'finalize'"),
                };

                // Initialize the registers.
                let mut registers = FinalizeRegisters::<N>::new(stack.get_finalize_types(finalize.name())?.clone());

                // Store the inputs.
                finalize.inputs().iter().map(|i| i.register()).zip_eq(inputs).try_for_each(|(register, input)| {
                    // Assign the input value to the register.
                    registers.store(stack, register, input.clone())
                })?;

                // Evaluate the commands.
                for command in finalize.commands() {
                    // If the command is a store, update the relevant state.
                    if let Command::Set(set) = command {
                        // Construct the `mapping ID`.
                        let mapping_id = N::hash_bhp1024(&(program_id, set.mapping_name()).to_bits_le())?;
                        updated_mapping_ids.insert(mapping_id);

                        // Load the key operand as a plaintext.
                        let key = registers.load_plaintext(stack, set.key())?;
                        // Load the value operand as a plaintext.
                        let value = Value::Plaintext(registers.load_plaintext(stack, set.value())?);

                        // Compute the key ID.
                        let key_id = N::hash_bhp1024(&(mapping_id, N::hash_bhp1024(&key.to_bits_le())?).to_bits_le())?;
                        // Compute the value ID.
                        let value_id = N::hash_bhp1024(&(key_id, N::hash_bhp1024(&value.to_bits_le())?).to_bits_le())?;

                        // Construct the update operation. If the key ID does not exist, insert it.
                        let operation = match vm.finalize_store().get_key_index(program_id, set.mapping_name(), &key)? {
                            Some(key_index) => {
                                // Add an update value operation.
                                MerkleTreeUpdate::UpdateValue(mapping_id, key_index as usize, key_id, value_id)
                            }
                            None => {
                                // Add an insert value operation.
                                // NOTE: We currently don't know if the key has already been inserted to the speculate state,
                                //  but we assign the operation as `Insert` and handle it downstream.
                                MerkleTreeUpdate::InsertValue(mapping_id, key_id, value_id)
                            }
                        };

                        operations.push((*program_id, operation));
                    }

                    // TODO (raychu86): Catch the panics here.
                    // Perform the speculative execution on the command.
                    command.speculate_finalize(stack, vm.finalize_store(), &mut registers, self)?;
                }
            }
        }

        // Update the log of operations.
        if !operations.is_empty() {
            self.operations.insert(transaction_id, operations);
        }

        Ok(())
    }

    /// Speculatively execute the given transaction.
    pub fn speculate_transaction<C: ConsensusStorage<N>>(
        &mut self,
        vm: &VM<N, C>,
        transaction: &Transaction<N>,
    ) -> Result<bool> {
        // Check that the `VM` state is correct.
        if vm.finalize_store().current_finalize_root() != self.latest_finalize_root {
            bail!("The latest finalize root does not match the VM finalize root");
        }

        // Check that the transaction has not been processed.
        if self.contains_transaction(&transaction.id()) {
            bail!("The transaction has already been processed");
        }

        // Add the transaction to the list of transactions.
        self.processed_transactions.push(transaction.id());

        // Perform the transaction mapping updates.
        match transaction {
            Transaction::Deploy(transaction_id, _, deployment, _fee) => {
                if let Err(err) = self.speculate_deployment(vm, *transaction_id, deployment) {
                    eprintln!("Failed to speculate transaction {transaction_id}: {err}");
                    return Ok(false);
                }

                // TODO (raychu86): Process the finalize updates in `fee`.
            }
            Transaction::Execute(transaction_id, execution, _fee) => {
                if let Err(err) = self.speculate_execution(vm, *transaction_id, execution) {
                    eprintln!("Failed to speculate transaction {transaction_id}: {err}");
                    return Ok(false);
                }

                // TODO (raychu86): Process the finalize updates in `fee`.
            }
        }

        // Add to the list of accepted transactions.
        self.accepted_transactions.push(transaction.id());

        Ok(true)
    }

    /// Speculatively execute the given transactions. Returns the transactions that were accepted.
    pub fn speculate_transactions<C: ConsensusStorage<N>>(
        &mut self,
        vm: &VM<N, C>,
        transactions: &[Transaction<N>],
    ) -> Result<Vec<N::TransactionID>> {
        let mut accepted_transactions = Vec::new();

        // Perform `speculate` on each transaction.
        for transaction in transactions {
            if self.speculate_transaction(vm, transaction)? {
                accepted_transactions.push(transaction.id());
            }
        }

        Ok(accepted_transactions)
    }

    /// Finalize the speculate and build the merkle trees.
    pub fn commit<C: ConsensusStorage<N>>(&self, vm: &VM<N, C>) -> Result<FinalizeTree<N>> {
        // Check that the `VM` state is correct.
        if vm.finalize_store().current_finalize_root() != self.latest_finalize_root {
            bail!("The latest finalize root does not match the VM finalize root");
        }

        // Fetch the current finalize tree.
        let finalize_tree_lock = vm.finalize_store().get_finalize_tree();
        let finalize_tree = finalize_tree_lock.read();

        // Collect the operations.
        let all_operations = self.operations.values().flatten().collect::<Vec<_>>();

        // If there are no operations, return the current finalize tree.
        if all_operations.is_empty() {
            return Ok(finalize_tree.clone());
        }

        // Filter the operations to see if there is any overlap that we can discard.
        let mut final_operations: IndexMap<ProgramID<N>, Vec<MerkleTreeUpdate<N>>> =
            IndexMap::with_capacity(all_operations.len());
        for (program_id, operation) in all_operations {
            let operations = final_operations.entry(*program_id).or_insert(Vec::new());

            // If you are updating a value that was inserted in this block, then you can just insert the final value.
            let operation_to_add =
                match operations.iter().any(|op| op.is_insert_value() && op.key_id() == operation.key_id()) {
                    true => match operation {
                        MerkleTreeUpdate::UpdateValue(mapping_id, _, key_id, value_id) => {
                            MerkleTreeUpdate::InsertValue(*mapping_id, *key_id, *value_id)
                        }
                        _ => *operation,
                    },
                    false => *operation,
                };

            // Remove the operations that have the same key ID, because they are now outdated.
            operations.retain(|op| op.key_id() != operation.key_id());

            // Add the operation to the list.
            operations.push(operation_to_add);
        }

        // Construct the updated program trees.
        let mut updated_program_trees = IndexMap::with_capacity(final_operations.len());
        for (program_id, operations) in final_operations {
            // Construct the program tree.
            let program_tree = vm.finalize_store().to_program_tree(&program_id, Some(&operations))?;

            updated_program_trees.insert(program_id, program_tree);
        }

        // Iterate through all the programs and construct the program trees.
        let mut updates = Vec::new();
        let mut appends = Vec::new();
        for (program_id, program_tree) in updated_program_trees.iter() {
            // Construct the leaf for the finalize tree.
            let leaf = program_tree.root().to_bits_le();

            // // Specify the update or append operation.
            match vm.finalize_store().contains_program(program_id)? {
                true => match vm.finalize_store().get_program_index(program_id)? {
                    Some(index) => updates.push((usize::try_from(index)?, leaf)),
                    None => bail!("No index found for program_id: {program_id}"),
                },
                false => appends.push(leaf),
            }
        }

        // Add new programs to the finalize tree.
        let mut updated_finalize_tree = finalize_tree.prepare_append(&appends)?;

        // Apply updates to the finalize tree.
        if !updates.is_empty() {
            // Sort the updates by descending order of indexes.
            updates.sort_by(|(a, _), (b, _)| b.cmp(a));

            // Apply the updates
            updated_finalize_tree.update_many(&updates)?;
        }

        // Return the finalize tree.
        Ok(updated_finalize_tree)
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

    use rand::{distributions::DistString, seq::SliceRandom};

    type CurrentNetwork = test_helpers::CurrentNetwork;

    pub const ITERATIONS: u32 = 8;

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
    fn test_speculate_duplicate() {
        let rng = &mut TestRng::default();

        let vm = test_helpers::sample_vm_with_genesis_block(rng);

        // Fetch a deployment transaction.
        let deployment_transaction = test_helpers::sample_deployment_transaction(rng);

        // Initialize the state speculator.
        let mut speculate = Speculate::new(vm.finalize_store().current_finalize_root());
        assert!(speculate.speculate_transaction(&vm, &deployment_transaction).unwrap());

        // Check that `speculate_transaction` will fail if you try with the same transaction.
        assert!(speculate.speculate_transaction(&vm, &deployment_transaction).is_err());

        // Check that `speculate_transactions` will fail if you try with duplicate transactions.
        let mut speculate = Speculate::new(vm.finalize_store().current_finalize_root());
        assert!(
            speculate.speculate_transactions(&vm, &[deployment_transaction.clone(), deployment_transaction]).is_err()
        );
    }

    #[test]
    fn test_speculate_deployment() {
        let rng = &mut TestRng::default();

        // Initialize the VM.
        let vm = test_helpers::sample_vm_with_genesis_block(rng);
        let duplicate_vm = test_helpers::sample_vm_with_genesis_block(rng);

        // Fetch a deployment transaction.
        let deployment_transaction = test_helpers::sample_deployment_transaction(rng);

        // Initialize the state speculator.
        let mut speculate = Speculate::new(vm.finalize_store().current_finalize_root());
        assert!(speculate.speculate_transaction(&vm, &deployment_transaction).unwrap());

        // Construct the new finalize tree.
        let new_finalize_tree = speculate.commit(&vm).unwrap();

        // Perform the naive vm finalize.
        let transactions = Transactions::from(&[deployment_transaction]);
        vm.finalize(&transactions, None).unwrap();
        duplicate_vm.finalize(&transactions, Some(speculate)).unwrap();

        // Fetch the expected finalize tree.
        let expected_finalize_root = vm.finalize_store().current_finalize_root();
        let duplicate_finalize_root = duplicate_vm.finalize_store().current_finalize_root();

        // Ensure that the finalize trees are the same.
        assert_eq!(expected_finalize_root, *new_finalize_tree.root());
        assert_eq!(expected_finalize_root, duplicate_finalize_root);
    }

    #[test]
    fn test_speculate_execution() {
        let rng = &mut TestRng::default();

        // Sample a private key and address for the caller.
        let caller_private_key = test_helpers::sample_genesis_private_key(rng);
        let caller_address = Address::try_from(&caller_private_key).unwrap();

        // Sample a private key and address for the recipient.
        let recipient_private_key = PrivateKey::new(rng).unwrap();
        let recipient_address = Address::try_from(&recipient_private_key).unwrap();

        // Initialize the VM.
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
        vm.add_next_block(&deployment_block, None).unwrap();

        // Construct a mint and a transfer.
        let mint_transaction =
            sample_mint_public(&vm, caller_private_key, &program_id, caller_address, 10, &mut unspent_records, rng);
        let transfer_transaction = sample_transfer_public(
            &vm,
            caller_private_key,
            &program_id,
            recipient_address,
            10,
            &mut unspent_records,
            rng,
        );

        // Initialize the state speculator.
        let mut speculate = Speculate::new(vm.finalize_store().current_finalize_root());
        assert!(speculate.speculate_transaction(&vm, &mint_transaction).unwrap());
        assert!(speculate.speculate_transaction(&vm, &transfer_transaction).unwrap());

        // Construct the new finalize tree.
        let new_finalize_tree = speculate.commit(&vm).unwrap();

        // Construct the next block
        let next_block = sample_next_block(
            &vm,
            &caller_private_key,
            &[mint_transaction, transfer_transaction],
            &deployment_block,
            &mut unspent_records,
            rng,
        )
        .unwrap();

        // Add the block to the vm.
        vm.add_next_block(&next_block, None).unwrap();

        // Fetch the expected finalize tree.
        let expected_finalize_root = vm.finalize_store().current_finalize_root();
        let finalize_tree_from_scratch = vm.finalize_store().to_finalize_tree().unwrap();

        // Ensure that the finalize trees are the same.
        assert_eq!(expected_finalize_root, *new_finalize_tree.root());
        assert_eq!(expected_finalize_root, *finalize_tree_from_scratch.root());
    }

    #[test]
    fn test_speculate_many() {
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
        vm.add_next_block(&deployment_block, None).unwrap();

        // Generate more records to use for the next block.
        let splits_block =
            generate_splits(&vm, &caller_private_key, &deployment_block, &mut unspent_records, rng).unwrap();

        // Add the splits block to the VM.
        vm.add_next_block(&splits_block, None).unwrap();

        // Construct the initial mint.
        let initial_mint =
            sample_mint_public(&vm, caller_private_key, &program_id, caller_address, 20, &mut unspent_records, rng);
        let initial_mint_block =
            sample_next_block(&vm, &caller_private_key, &[initial_mint], &splits_block, &mut unspent_records, rng)
                .unwrap();

        // Add the block to the vm.
        vm.add_next_block(&initial_mint_block, None).unwrap();

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

        // Starting Balance = 20
        // Mint_10 -> Balance = 20 + 10  = 30
        // Transfer_10 -> Balance = 30 - 10 = 20
        // Transfer_20 -> Balance = 20 - 20
        {
            let mut speculate = Speculate::new(vm.finalize_store().current_finalize_root());

            let transactions = [mint_10.clone(), transfer_10.clone(), transfer_20.clone()];

            // Assert that all transactions are valid.
            assert_eq!(
                vec![mint_10.id(), transfer_10.id(), transfer_20.id()],
                speculate.speculate_transactions(&vm, &transactions).unwrap()
            );
        }

        // Starting Balance = 20
        // Transfer_20 -> Balance = 20 - 20 = 0
        // Mint_10 -> Balance = 0 + 10 = 10
        // Mint_20 -> Balance = 10 + 20 = 30
        // Transfer_30 -> Balance = 30 - 30 = 0
        {
            let mut speculate = Speculate::new(vm.finalize_store().current_finalize_root());

            let transactions = [transfer_20.clone(), mint_10.clone(), mint_20.clone(), transfer_30.clone()];

            // Assert that all transactions are valid.
            assert_eq!(
                vec![transfer_20.id(), mint_10.id(), mint_20.id(), transfer_30.id()],
                speculate.speculate_transactions(&vm, &transactions).unwrap()
            );
        }

        // Starting Balance = 20
        // Transfer_20 -> Balance = 20 - 20 = 0
        // Transfer_10 -> Balance = 0 - 10 = -10 (should fail)
        {
            let transactions = [transfer_20.clone(), transfer_10.clone()];

            // Assert that the first transaction is valid.
            let mut speculate = Speculate::new(vm.finalize_store().current_finalize_root());
            assert_eq!(vec![transfer_20.id()], speculate.speculate_transactions(&vm, &transactions).unwrap());
        }

        // Starting Balance = 20
        // Mint_20 -> Balance = 20 + 20
        // Transfer_30 -> Balance = 40 - 30 = 10
        // Transfer_20 -> Balance = 10 - 20 = -10 (should fail)
        // Transfer_10 -> Balance = 10 - 10 = 0
        {
            let transactions = [mint_20.clone(), transfer_30.clone(), transfer_20, transfer_10.clone()];

            // Assert that the first transaction is valid.
            let mut speculate = Speculate::new(vm.finalize_store().current_finalize_root());
            assert_eq!(
                vec![mint_20.id(), transfer_30.id(), transfer_10.id()],
                speculate.speculate_transactions(&vm, &transactions).unwrap()
            );
        }
    }

    #[test]
    fn test_speculate_multiple_programs() {
        let rng = &mut TestRng::default();

        // Sample a private key and address for the caller.
        let caller_private_key = test_helpers::sample_genesis_private_key(rng);
        let caller_address = Address::try_from(&caller_private_key).unwrap();

        // Initialize the vm.
        let vm = test_helpers::sample_vm_with_genesis_block(rng);

        // Construct the next block.
        let genesis =
            vm.block_store().get_block(&vm.block_store().get_block_hash(0).unwrap().unwrap()).unwrap().unwrap();

        // Get the unspent records.
        let mut unspent_records = genesis
            .transitions()
            .cloned()
            .flat_map(Transition::into_records)
            .map(|(_, record)| record)
            .collect::<Vec<_>>();

        // Sample program 1.
        let (program_1, block_1) =
            new_program_deployment(&vm, &caller_private_key, &genesis, &mut unspent_records, rng).unwrap();
        vm.add_next_block(&block_1, None).unwrap();

        // Sample program 2.
        let (program_2, block_2) =
            new_program_deployment(&vm, &caller_private_key, &block_1, &mut unspent_records, rng).unwrap();
        vm.add_next_block(&block_2, None).unwrap();

        // Sample program 3.
        let (program_3, block_3) =
            new_program_deployment(&vm, &caller_private_key, &block_2, &mut unspent_records, rng).unwrap();
        vm.add_next_block(&block_3, None).unwrap();

        // Ensure that the finalize trees are the same.
        assert_eq!(
            vm.finalize_store().current_finalize_root(),
            *vm.finalize_store().to_finalize_tree().unwrap().root()
        );

        // Generate more records to use for the next block.
        let splits_block = generate_splits(&vm, &caller_private_key, &block_3, &mut unspent_records, rng).unwrap();

        // Add the splits block to the VM.
        vm.add_next_block(&splits_block, None).unwrap();

        // Generate many transactions.
        let programs = [program_1, program_2, program_3];

        let mut transactions = Vec::with_capacity(ITERATIONS as usize);

        for _ in 0..ITERATIONS {
            // Pick the program to create a transaction for.
            let program = programs.choose(rng).unwrap();

            // Generate a mint or transfer transaction
            let transaction = match rng.gen() {
                true => sample_mint_public(
                    &vm,
                    caller_private_key,
                    program,
                    caller_address,
                    rng.gen_range(50..100),
                    &mut unspent_records,
                    rng,
                ),
                false => sample_transfer_public(
                    &vm,
                    caller_private_key,
                    program,
                    caller_address,
                    rng.gen_range(1..50),
                    &mut unspent_records,
                    rng,
                ),
            };

            transactions.push(transaction);
        }

        // Initialize the state speculator.
        let mut speculate = Speculate::new(vm.finalize_store().current_finalize_root());
        let accepted_transactions = speculate.speculate_transactions(&vm, &transactions).unwrap();

        // Keep the transactions that are accepted.
        let transactions: Vec<_> =
            transactions.into_iter().filter(|transaction| accepted_transactions.contains(&transaction.id())).collect();

        // Sample the next block with the transactions.
        let next_block =
            sample_next_block(&vm, &caller_private_key, &transactions, &splits_block, &mut unspent_records, rng)
                .unwrap();

        // Add the block to the vm.
        vm.add_next_block(&next_block, Some(speculate)).unwrap();

        // Ensure that the finalize trees are the same.
        assert_eq!(
            vm.finalize_store().current_finalize_root(),
            *vm.finalize_store().to_finalize_tree().unwrap().root()
        );
    }
}
