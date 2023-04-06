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

use crate::{
    program::finalize::Command,
    ConsensusStorage,
    Deployment,
    Execution,
    FinalizeRegisters,
    Load,
    Store,
    Transaction,
    VM,
};

// TODO (raychu86): Move this out of `store/program`

/// The speculative executor for the program state.
#[derive(Clone)]
pub struct Speculate<N: Network> {
    /// The latest storage root.
    /// This is used to ensure that the speculate state is building off the same state.
    pub latest_storage_root: Field<N>,

    /// The list of transactions that have been processed. Including ones that have been rejected.
    pub processed_transactions: Vec<N::TransactionID>,

    /// The list of accepted transactions that have been processed.
    pub accepted_transactions: Vec<N::TransactionID>,

    /// The values updated in the speculate state. (`program ID`, (`mapping name`, (`key`, `value`)))
    pub speculate_state: IndexMap<ProgramID<N>, IndexMap<Identifier<N>, IndexMap<Vec<u8>, Value<N>>>>,

    /// The operations being performed.
    pub operations: IndexMap<N::TransactionID, Vec<(ProgramID<N>, MerkleTreeUpdate<N>)>>,

    // The following values will be updated in the `Self::commit` function.
    /// The updated program trees.
    pub updated_program_trees: Option<IndexMap<ProgramID<N>, ProgramTree<N>>>,
}

impl<N: Network> Speculate<N> {
    /// Initializes a new instance of `Speculate`.
    pub fn new(latest_storage_root: Field<N>) -> Self {
        Self {
            latest_storage_root,
            processed_transactions: Default::default(),
            accepted_transactions: Default::default(),
            speculate_state: Default::default(),
            operations: Default::default(),
            updated_program_trees: None,
        }
    }

    /// Returns `true` if the transaction has been processed.
    pub fn contains_transaction(&self, transaction_id: &N::TransactionID) -> bool {
        self.processed_transactions.contains(transaction_id)
            || self.accepted_transactions.contains(transaction_id)
            || self.operations.contains_key(transaction_id)
    }

    /// Returns `true` if the speculate state is complete.
    pub fn is_complete(&self) -> bool {
        self.updated_program_trees.is_some()
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
        self.operations.insert(transaction_id, operations);

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
                    if let Command::Store(store) = command {
                        // Construct the `mapping ID`.
                        let mapping_id = N::hash_bhp1024(&(program_id, store.mapping_name()).to_bits_le())?;
                        updated_mapping_ids.insert(mapping_id);

                        // Load the key operand as a plaintext.
                        let key = registers.load_plaintext(stack, store.key())?;
                        // Load the value operand as a plaintext.
                        let value = Value::Plaintext(registers.load_plaintext(stack, store.value())?);

                        // Compute the key ID.
                        let key_id = N::hash_bhp1024(&(mapping_id, N::hash_bhp1024(&key.to_bits_le())?).to_bits_le())?;
                        // Compute the value ID.
                        let value_id = N::hash_bhp1024(&(key_id, N::hash_bhp1024(&value.to_bits_le())?).to_bits_le())?;

                        // Construct the update operation. If the key ID does not exist, insert it.
                        let operation =
                            match vm.program_store().get_key_index(program_id, store.mapping_name(), &key)? {
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

                    // Perform the speculative execution on the command.
                    command.speculate_finalize(stack, vm.program_store(), &mut registers, self)?;
                }
            }
        }

        // Update the log of operations.
        self.operations.insert(transaction_id, operations);

        Ok(())
    }

    /// Speculatively execute the given transaction.
    pub fn speculate_transaction<C: ConsensusStorage<N>>(
        &mut self,
        vm: &VM<N, C>,
        transaction: &Transaction<N>,
    ) -> Result<bool> {
        // Ensure that the speculate has not already been completed.
        if self.is_complete() {
            bail!("Speculate has already been completed ");
        }

        // Check that the `VM` state is correct.
        if vm.program_store().current_storage_root() != self.latest_storage_root {
            bail!("The latest storage root does not match the VM storage root");
        }

        // Check that the transaction has not been processed.
        if self.contains_transaction(&transaction.id()) {
            bail!("The transaction has already been processed");
        }

        // Check that the transaction is valid.
        // TODO (raychu86): Add finalize checks in VM::verify_execution and VM::verify_deployment.
        if !vm.verify_transaction(transaction) {
            bail!("The transaction is invalid");
        }

        // Add the transaction to the list of transactions.
        self.processed_transactions.push(transaction.id());

        // Perform the transaction mapping updates.
        match transaction {
            Transaction::Deploy(transaction_id, deployment, _fee) => {
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

    /// Finalize the speculate and build the merkle trees.
    pub fn commit<C: ConsensusStorage<N>>(&mut self, vm: &VM<N, C>) -> Result<()> {
        // Ensure that the speculate has not already been completed.
        if self.is_complete() {
            bail!("Speculate has already been completed ");
        }

        // Check that the `VM` state is correct.
        if vm.program_store().current_storage_root() != self.latest_storage_root {
            bail!("The latest storage root does not match the VM storage root");
        }

        // Collect the operations.
        let all_operations = self.operations.values().flatten().collect::<Vec<_>>();

        // Filter the operations to see if there is any overlap that we can discard.
        let mut final_operations: IndexMap<ProgramID<N>, Vec<MerkleTreeUpdate<N>>> =
            IndexMap::with_capacity(all_operations.len());
        for (program_id, operation) in all_operations {
            let operations = final_operations.entry(*program_id).or_insert(Vec::new());

            // Remove the operations that have the same key ID, because they are now outdated.
            operations.retain(|op| op.key_id() != op.key_id());

            // Add the operation to the list.
            operations.push(*operation);
        }

        // Construct the updated program trees.
        let mut program_trees = IndexMap::with_capacity(final_operations.len());
        for (program_id, operations) in final_operations {
            // Construct the program tree.
            let program_tree = vm.program_store().storage.to_program_tree(&program_id, Some(&operations))?;

            program_trees.insert(program_id, program_tree);
        }

        // Update the program trees.
        self.updated_program_trees = Some(program_trees);

        Ok(())
    }
}
