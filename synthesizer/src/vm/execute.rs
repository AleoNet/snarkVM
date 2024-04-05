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

#![allow(clippy::too_many_arguments)]

use super::*;

impl<N: Network, C: ConsensusStorage<N>> VM<N, C> {
    /// Returns a new execute transaction.
    ///
    /// If a `fee_record` is provided, then a private fee will be included in the transaction;
    /// otherwise, a public fee will be included in the transaction.
    ///
    /// The `priority_fee_in_microcredits` is an additional fee **on top** of the execution fee.
    pub fn execute<R: Rng + CryptoRng>(
        &self,
        private_key: &PrivateKey<N>,
        (program_id, function_name): (impl TryInto<ProgramID<N>>, impl TryInto<Identifier<N>>),
        inputs: impl ExactSizeIterator<Item = impl TryInto<Value<N>>>,
        fee_record: Option<Record<N, Plaintext<N>>>,
        priority_fee_in_microcredits: u64,
        query: Option<Query<N, C::BlockStorage>>,
        rng: &mut R,
    ) -> Result<Transaction<N>> {
        // Compute the authorization.
        let authorization = self.authorize(private_key, program_id, function_name, inputs, rng)?;
        // Determine if a fee is required.
        let is_fee_required = !authorization.is_split();
        // Determine if a priority fee is declared.
        let is_priority_fee_declared = priority_fee_in_microcredits > 0;
        // Compute the execution.
        let execution = self.execute_authorization_raw(authorization, query.clone(), rng)?;
        // Compute the fee.
        let fee = match is_fee_required || is_priority_fee_declared {
            true => {
                // Compute the minimum execution cost.
                let (minimum_execution_cost, (_, _)) = execution_cost(&self.process().read(), &execution)?;
                // Compute the execution ID.
                let execution_id = execution.to_execution_id()?;
                // Authorize the fee.
                let authorization = match fee_record {
                    Some(record) => self.authorize_fee_private(
                        private_key,
                        record,
                        minimum_execution_cost,
                        priority_fee_in_microcredits,
                        execution_id,
                        rng,
                    )?,
                    None => self.authorize_fee_public(
                        private_key,
                        minimum_execution_cost,
                        priority_fee_in_microcredits,
                        execution_id,
                        rng,
                    )?,
                };
                // Execute the fee.
                Some(self.execute_fee_authorization_raw(authorization, query, rng)?)
            }
            false => None,
        };
        // Return the execute transaction.
        Transaction::from_execution(execution, fee)
    }

    /// Returns a new execute transaction for the given authorization.
    pub fn execute_authorization<R: Rng + CryptoRng>(
        &self,
        execute_authorization: Authorization<N>,
        fee_authorization: Option<Authorization<N>>,
        query: Option<Query<N, C::BlockStorage>>,
        rng: &mut R,
    ) -> Result<Transaction<N>> {
        // Compute the execution.
        let execution = self.execute_authorization_raw(execute_authorization, query.clone(), rng)?;
        // Compute the fee.
        let fee = match fee_authorization {
            Some(authorization) => Some(self.execute_fee_authorization_raw(authorization, query, rng)?),
            None => None,
        };
        // Return the execute transaction.
        Transaction::from_execution(execution, fee)
    }

    /// Returns a new fee for the given authorization.
    pub fn execute_fee_authorization<R: Rng + CryptoRng>(
        &self,
        authorization: Authorization<N>,
        query: Option<Query<N, C::BlockStorage>>,
        rng: &mut R,
    ) -> Result<Fee<N>> {
        debug_assert!(authorization.is_fee_private() || authorization.is_fee_public(), "Expected a fee authorization");
        self.execute_fee_authorization_raw(authorization, query, rng)
    }
}

impl<N: Network, C: ConsensusStorage<N>> VM<N, C> {
    /// Executes a call to the program function for the given authorization.
    /// Returns the execution.
    #[inline]
    fn execute_authorization_raw<R: Rng + CryptoRng>(
        &self,
        authorization: Authorization<N>,
        query: Option<Query<N, C::BlockStorage>>,
        rng: &mut R,
    ) -> Result<Execution<N>> {
        let timer = timer!("VM::execute_authorization_raw");

        // Construct the locator of the main function.
        let locator = {
            let request = authorization.peek_next()?;
            Locator::new(*request.program_id(), *request.function_name()).to_string()
        };
        // Prepare the query.
        let query = match query {
            Some(query) => query,
            None => Query::VM(self.block_store().clone()),
        };
        lap!(timer, "Prepare the query");

        macro_rules! logic {
            ($process:expr, $network:path, $aleo:path) => {{
                // Prepare the authorization.
                let authorization = cast_ref!(authorization as Authorization<$network>);
                // Execute the call.
                let (_, mut trace) = $process.execute::<$aleo, _>(authorization.clone(), rng)?;
                lap!(timer, "Execute the call");

                // Prepare the assignments.
                cast_mut_ref!(trace as Trace<N>).prepare(query)?;
                lap!(timer, "Prepare the assignments");

                // Compute the proof and construct the execution.
                let execution = trace.prove_execution::<$aleo, _>(&locator, rng)?;
                lap!(timer, "Compute the proof");

                // Return the execution.
                Ok(cast_ref!(execution as Execution<N>).clone())
            }};
        }

        // Execute the authorization.
        let result = process!(self, logic);
        finish!(timer, "Execute the authorization");
        result
    }

    /// Executes a call to the program function for the given fee authorization.
    /// Returns the fee.
    #[inline]
    fn execute_fee_authorization_raw<R: Rng + CryptoRng>(
        &self,
        authorization: Authorization<N>,
        query: Option<Query<N, C::BlockStorage>>,
        rng: &mut R,
    ) -> Result<Fee<N>> {
        let timer = timer!("VM::execute_fee_authorization_raw");

        // Prepare the query.
        let query = match query {
            Some(query) => query,
            None => Query::VM(self.block_store().clone()),
        };
        lap!(timer, "Prepare the query");

        macro_rules! logic {
            ($process:expr, $network:path, $aleo:path) => {{
                // Prepare the authorization.
                let authorization = cast_ref!(authorization as Authorization<$network>);
                // Execute the call.
                let (_, mut trace) = $process.execute::<$aleo, _>(authorization.clone(), rng)?;
                lap!(timer, "Execute the call");

                // Prepare the assignments.
                cast_mut_ref!(trace as Trace<N>).prepare(query)?;
                lap!(timer, "Prepare the assignments");

                // Compute the proof and construct the fee.
                let fee = trace.prove_fee::<$aleo, _>(rng)?;
                lap!(timer, "Compute the proof");

                // Return the fee.
                Ok(cast_ref!(fee as Fee<N>).clone())
            }};
        }

        // Execute the authorization.
        let result = process!(self, logic);
        finish!(timer, "Execute the authorization");
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::{
        account::{Address, ViewKey},
        network::MainnetV0,
        program::{Ciphertext, Value},
        types::Field,
    };
    use ledger_block::Transition;
    use ledger_store::helpers::memory::ConsensusMemory;
    use synthesizer_process::cost_per_command;
    use synthesizer_program::StackProgram;

    use indexmap::IndexMap;

    type CurrentNetwork = MainnetV0;

    fn prepare_vm(
        rng: &mut TestRng,
    ) -> Result<(
        VM<CurrentNetwork, ConsensusMemory<CurrentNetwork>>,
        IndexMap<Field<CurrentNetwork>, Record<CurrentNetwork, Ciphertext<CurrentNetwork>>>,
    )> {
        // Initialize the genesis block.
        let genesis = crate::vm::test_helpers::sample_genesis_block(rng);

        // Fetch the unspent records.
        let records = genesis.transitions().cloned().flat_map(Transition::into_records).collect::<IndexMap<_, _>>();

        // Initialize the genesis block.
        let genesis = crate::vm::test_helpers::sample_genesis_block(rng);

        // Initialize the VM.
        let vm = crate::vm::test_helpers::sample_vm();
        // Update the VM.
        vm.add_next_block(&genesis).unwrap();

        Ok((vm, records))
    }

    #[test]
    fn test_bond_public_transaction_size() {
        let rng = &mut TestRng::default();

        // Initialize a new caller.
        let caller_private_key = crate::vm::test_helpers::sample_genesis_private_key(rng);
        let address = Address::try_from(&caller_private_key).unwrap();

        // Prepare the VM and records.
        let (vm, _) = prepare_vm(rng).unwrap();

        // Prepare the inputs.
        let inputs = [
            Value::<CurrentNetwork>::from_str(&address.to_string()).unwrap(),
            Value::<CurrentNetwork>::from_str(&address.to_string()).unwrap(),
            Value::<CurrentNetwork>::from_str("1_000_000u64").unwrap(),
        ]
        .into_iter();

        // Execute.
        let transaction =
            vm.execute(&caller_private_key, ("credits.aleo", "bond_public"), inputs, None, 0, None, rng).unwrap();

        // Ensure the transaction is a bond public transition.
        assert_eq!(transaction.transitions().count(), 2);
        assert!(transaction.transitions().take(1).next().unwrap().is_bond_public());

        // Assert the size of the transaction.
        let transaction_size_in_bytes = transaction.to_bytes_le().unwrap().len();
        assert_eq!(2970, transaction_size_in_bytes, "Update me if serialization has changed");

        // Assert the size of the execution.
        assert!(matches!(transaction, Transaction::Execute(_, _, _)));
        if let Transaction::Execute(_, execution, _) = &transaction {
            let execution_size_in_bytes = execution.to_bytes_le().unwrap().len();
            assert_eq!(1519, execution_size_in_bytes, "Update me if serialization has changed");
        }
    }

    #[test]
    fn test_unbond_public_transaction_size() {
        let rng = &mut TestRng::default();

        // Initialize a new caller.
        let caller_private_key = crate::vm::test_helpers::sample_genesis_private_key(rng);

        // Prepare the VM and records.
        let (vm, _) = prepare_vm(rng).unwrap();

        // Prepare the inputs.
        let inputs = [Value::<CurrentNetwork>::from_str("1u64").unwrap()].into_iter();

        // Execute.
        let transaction =
            vm.execute(&caller_private_key, ("credits.aleo", "unbond_public"), inputs, None, 0, None, rng).unwrap();

        // Ensure the transaction is an unbond public transition.
        assert_eq!(transaction.transitions().count(), 2);
        assert!(transaction.transitions().take(1).next().unwrap().is_unbond_public());

        // Assert the size of the transaction.
        let transaction_size_in_bytes = transaction.to_bytes_le().unwrap().len();
        assert_eq!(2760, transaction_size_in_bytes, "Update me if serialization has changed");

        // Assert the size of the execution.
        assert!(matches!(transaction, Transaction::Execute(_, _, _)));
        if let Transaction::Execute(_, execution, _) = &transaction {
            let execution_size_in_bytes = execution.to_bytes_le().unwrap().len();
            assert_eq!(1309, execution_size_in_bytes, "Update me if serialization has changed");
        }
    }

    #[test]
    fn test_transfer_private_transaction_size() {
        let rng = &mut TestRng::default();

        // Initialize a new caller.
        let caller_private_key = crate::vm::test_helpers::sample_genesis_private_key(rng);
        let caller_view_key = ViewKey::try_from(&caller_private_key).unwrap();
        let address = Address::try_from(&caller_private_key).unwrap();

        // Prepare the VM and records.
        let (vm, records) = prepare_vm(rng).unwrap();

        // Fetch the unspent record.
        let record = records.values().next().unwrap().decrypt(&caller_view_key).unwrap();

        // Prepare the inputs.
        let inputs = [
            Value::<CurrentNetwork>::Record(record),
            Value::<CurrentNetwork>::from_str(&address.to_string()).unwrap(),
            Value::<CurrentNetwork>::from_str("1u64").unwrap(),
        ]
        .into_iter();

        // Execute.
        let transaction =
            vm.execute(&caller_private_key, ("credits.aleo", "transfer_private"), inputs, None, 0, None, rng).unwrap();

        // Assert the size of the transaction.
        let transaction_size_in_bytes = transaction.to_bytes_le().unwrap().len();
        assert_eq!(3693, transaction_size_in_bytes, "Update me if serialization has changed");

        // Assert the size of the execution.
        assert!(matches!(transaction, Transaction::Execute(_, _, _)));
        if let Transaction::Execute(_, execution, _) = &transaction {
            let execution_size_in_bytes = execution.to_bytes_le().unwrap().len();
            assert_eq!(2242, execution_size_in_bytes, "Update me if serialization has changed");
        }
    }

    #[test]
    fn test_transfer_public_transaction_size() {
        let rng = &mut TestRng::default();

        // Initialize a new caller.
        let caller_private_key = crate::vm::test_helpers::sample_genesis_private_key(rng);
        let address = Address::try_from(&caller_private_key).unwrap();

        // Prepare the VM and records.
        let (vm, _) = prepare_vm(rng).unwrap();

        // Prepare the inputs.
        let inputs = [
            Value::<CurrentNetwork>::from_str(&address.to_string()).unwrap(),
            Value::<CurrentNetwork>::from_str("1u64").unwrap(),
        ]
        .into_iter();

        // Execute.
        let transaction =
            vm.execute(&caller_private_key, ("credits.aleo", "transfer_public"), inputs, None, 0, None, rng).unwrap();

        // Assert the size of the transaction.
        let transaction_size_in_bytes = transaction.to_bytes_le().unwrap().len();
        assert_eq!(2871, transaction_size_in_bytes, "Update me if serialization has changed");

        // Assert the size of the execution.
        assert!(matches!(transaction, Transaction::Execute(_, _, _)));
        if let Transaction::Execute(_, execution, _) = &transaction {
            let execution_size_in_bytes = execution.to_bytes_le().unwrap().len();
            assert_eq!(1420, execution_size_in_bytes, "Update me if serialization has changed");
        }
    }

    #[test]
    fn test_transfer_public_as_signer_transaction_size() {
        let rng = &mut TestRng::default();

        // Initialize a new signer.
        let signer = crate::vm::test_helpers::sample_genesis_private_key(rng);
        let address = Address::try_from(&signer).unwrap();

        // Prepare the VM and records.
        let (vm, _) = prepare_vm(rng).unwrap();

        // Prepare the inputs.
        let inputs = [
            Value::<CurrentNetwork>::from_str(&address.to_string()).unwrap(),
            Value::<CurrentNetwork>::from_str("1u64").unwrap(),
        ]
        .into_iter();

        // Execute.
        let transaction =
            vm.execute(&signer, ("credits.aleo", "transfer_public_as_signer"), inputs, None, 0, None, rng).unwrap();

        // Assert the size of the transaction.
        let transaction_size_in_bytes = transaction.to_bytes_le().unwrap().len();
        assert_eq!(2891, transaction_size_in_bytes, "Update me if serialization has changed");

        // Assert the size of the execution.
        assert!(matches!(transaction, Transaction::Execute(_, _, _)));
        if let Transaction::Execute(_, execution, _) = &transaction {
            let execution_size_in_bytes = execution.to_bytes_le().unwrap().len();
            assert_eq!(1440, execution_size_in_bytes, "Update me if serialization has changed");
        }
    }

    #[test]
    fn test_join_transaction_size() {
        let rng = &mut TestRng::default();

        // Initialize a new caller.
        let caller_private_key = crate::vm::test_helpers::sample_genesis_private_key(rng);
        let caller_view_key = ViewKey::try_from(&caller_private_key).unwrap();

        // Prepare the VM and records.
        let (vm, records) = prepare_vm(rng).unwrap();

        // Fetch the unspent records.
        let mut records = records.values();
        let record_1 = records.next().unwrap().decrypt(&caller_view_key).unwrap();
        let record_2 = records.next().unwrap().decrypt(&caller_view_key).unwrap();

        // Prepare the inputs.
        let inputs = [Value::<CurrentNetwork>::Record(record_1), Value::<CurrentNetwork>::Record(record_2)].into_iter();

        // Execute.
        let transaction =
            vm.execute(&caller_private_key, ("credits.aleo", "join"), inputs, None, 0, None, rng).unwrap();

        // Assert the size of the transaction.
        let transaction_size_in_bytes = transaction.to_bytes_le().unwrap().len();
        assert_eq!(3538, transaction_size_in_bytes, "Update me if serialization has changed");

        // Assert the size of the execution.
        assert!(matches!(transaction, Transaction::Execute(_, _, _)));
        if let Transaction::Execute(_, execution, _) = &transaction {
            let execution_size_in_bytes = execution.to_bytes_le().unwrap().len();
            assert_eq!(2087, execution_size_in_bytes, "Update me if serialization has changed");
        }
    }

    #[test]
    fn test_split_transaction_size() {
        let rng = &mut TestRng::default();

        // Initialize a new caller.
        let caller_private_key = crate::vm::test_helpers::sample_genesis_private_key(rng);
        let caller_view_key = ViewKey::try_from(&caller_private_key).unwrap();

        // Prepare the VM and records.
        let (vm, records) = prepare_vm(rng).unwrap();

        // Fetch the unspent record.
        let record = records.values().next().unwrap().decrypt(&caller_view_key).unwrap();

        // Prepare the inputs.
        let inputs =
            [Value::<CurrentNetwork>::Record(record), Value::<CurrentNetwork>::from_str("1u64").unwrap()].into_iter();

        // Execute.
        let transaction =
            vm.execute(&caller_private_key, ("credits.aleo", "split"), inputs, None, 0, None, rng).unwrap();

        // Ensure the transaction is a split transition.
        assert_eq!(transaction.transitions().count(), 1);
        assert!(transaction.transitions().next().unwrap().is_split());

        // Assert the size of the transaction.
        let transaction_size_in_bytes = transaction.to_bytes_le().unwrap().len();
        assert_eq!(2166, transaction_size_in_bytes, "Update me if serialization has changed");

        // Assert the size of the execution.
        assert!(matches!(transaction, Transaction::Execute(_, _, _)));
        if let Transaction::Execute(_, execution, _) = &transaction {
            let execution_size_in_bytes = execution.to_bytes_le().unwrap().len();
            assert_eq!(2131, execution_size_in_bytes, "Update me if serialization has changed");
        }
    }

    #[test]
    fn test_fee_private_transition_size() {
        let rng = &mut TestRng::default();

        // Retrieve a fee transaction.
        let transaction = ledger_test_helpers::sample_fee_private_transaction(rng);
        // Retrieve the fee.
        let fee = match transaction {
            Transaction::Fee(_, fee) => fee,
            _ => panic!("Expected a fee transaction"),
        };

        // Ensure the transition is a fee transition.
        assert!(fee.is_fee_private());

        // Assert the size of the transition.
        let fee_size_in_bytes = fee.to_bytes_le().unwrap().len();
        assert_eq!(2043, fee_size_in_bytes, "Update me if serialization has changed");
    }

    #[test]
    fn test_fee_public_transition_size() {
        let rng = &mut TestRng::default();

        // Retrieve a fee transaction.
        let transaction = ledger_test_helpers::sample_fee_public_transaction(rng);
        // Retrieve the fee.
        let fee = match transaction {
            Transaction::Fee(_, fee) => fee,
            _ => panic!("Expected a fee transaction"),
        };

        // Ensure the transition is a fee transition.
        assert!(fee.is_fee_public());

        // Assert the size of the transition.
        let fee_size_in_bytes = fee.to_bytes_le().unwrap().len();
        assert_eq!(1416, fee_size_in_bytes, "Update me if serialization has changed");
    }

    #[test]
    fn test_wide_nested_execution_cost() {
        // Initialize an RNG.
        let rng = &mut TestRng::default();

        // Initialize a new caller.
        let caller_private_key = crate::vm::test_helpers::sample_genesis_private_key(rng);

        // Prepare the VM.
        let (vm, _) = prepare_vm(rng).unwrap();

        // Construct the child program.
        let child_program = Program::from_str(
            r"
program child.aleo;
mapping data:
    key as field.public;
    value as field.public;
function test:
    input r0 as field.public;
    input r1 as field.public;
    async test r0 r1 into r2;
    output r2 as child.aleo/test.future;
finalize test:
    input r0 as field.public;
    input r1 as field.public;
    hash.bhp256 r0 into r2 as field;
    hash.bhp256 r1 into r3 as field;
    set r2 into data[r3];",
        )
        .unwrap();

        // Deploy the program.
        let transaction = vm.deploy(&caller_private_key, &child_program, None, 0, None, rng).unwrap();

        // Construct the next block.
        let next_block = crate::test_helpers::sample_next_block(&vm, &caller_private_key, &[transaction], rng).unwrap();

        // Add the next block to the VM.
        vm.add_next_block(&next_block).unwrap();

        // Construct the parent program.
        let parent_program = Program::from_str(
            r"
import child.aleo;
program parent.aleo;
function test:
    call child.aleo/test 0field 1field into r0;
    call child.aleo/test 2field 3field into r1;
    call child.aleo/test 4field 5field into r2;
    call child.aleo/test 6field 7field into r3;
    call child.aleo/test 8field 9field into r4;
    call child.aleo/test 10field 11field into r5;
    call child.aleo/test 12field 13field into r6;
    call child.aleo/test 14field 15field into r7;
    call child.aleo/test 16field 17field into r8;
    call child.aleo/test 18field 19field into r9;
    call child.aleo/test 20field 21field into r10;
    call child.aleo/test 22field 23field into r11;
    call child.aleo/test 24field 25field into r12;
    call child.aleo/test 26field 27field into r13;
    call child.aleo/test 28field 29field into r14;
    call child.aleo/test 30field 31field into r15;
    async test r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 into r16;
    output r16 as parent.aleo/test.future;
finalize test:
    input r0 as child.aleo/test.future;
    input r1 as child.aleo/test.future;
    input r2 as child.aleo/test.future;
    input r3 as child.aleo/test.future;
    input r4 as child.aleo/test.future;
    input r5 as child.aleo/test.future;
    input r6 as child.aleo/test.future;
    input r7 as child.aleo/test.future;
    input r8 as child.aleo/test.future;
    input r9 as child.aleo/test.future;
    input r10 as child.aleo/test.future;
    input r11 as child.aleo/test.future;
    input r12 as child.aleo/test.future;
    input r13 as child.aleo/test.future;
    input r14 as child.aleo/test.future;
    input r15 as child.aleo/test.future;
    await r0;
    await r1;
    await r2;
    await r3;
    await r4;
    await r5;
    await r6;
    await r7;
    await r8;
    await r9;
    await r10;
    await r11;
    await r12;
    await r13;
    await r14;
    await r15;",
        )
        .unwrap();

        // Deploy the program.
        let transaction = vm.deploy(&caller_private_key, &parent_program, None, 0, None, rng).unwrap();

        // Construct the next block.
        let next_block = crate::test_helpers::sample_next_block(&vm, &caller_private_key, &[transaction], rng).unwrap();

        // Add the next block to the VM.
        vm.add_next_block(&next_block).unwrap();

        // Execute the parent program.
        let Transaction::Execute(_, execution, _) = vm
            .execute(&caller_private_key, ("parent.aleo", "test"), Vec::<Value<_>>::new().iter(), None, 0, None, rng)
            .unwrap()
        else {
            unreachable!("VM::execute always produces an `Execution`")
        };

        // Check that the number of transitions is correct.
        // Change me if the `MAX_INPUTS` changes.
        assert_eq!(execution.transitions().len(), <CurrentNetwork as Network>::MAX_INPUTS + 1);

        // Get the finalize cost of the execution.
        let (_, (_, finalize_cost)) = execution_cost(&vm.process().read(), &execution).unwrap();

        // Compute the expected cost as the sum of the cost in microcredits of each command in each finalize block of each transition in the execution.
        let mut expected_cost = 0;
        for transition in execution.transitions() {
            // Get the program ID and name of the transition.
            let program_id = transition.program_id();
            let function_name = transition.function_name();
            // Get the stack.
            let stack = vm.process().read().get_stack(program_id).unwrap().clone();
            // Get the finalize block of the transition and sum the cost of each command.
            let cost = match stack.get_function(function_name).unwrap().finalize_logic() {
                None => 0,
                Some(finalize_logic) => {
                    // Aggregate the cost of all commands in the program.
                    finalize_logic
                        .commands()
                        .iter()
                        .map(|command| cost_per_command(&stack, finalize_logic, command))
                        .try_fold(0u64, |acc, res| {
                            res.and_then(|x| acc.checked_add(x).ok_or(anyhow!("Finalize cost overflowed")))
                        })
                        .unwrap()
                }
            };
            // Add the cost to the total cost.
            expected_cost += cost;
        }

        // Check that the finalize cost is equal to the expected cost.
        assert_eq!(finalize_cost, expected_cost);
    }

    #[test]
    fn test_deep_nested_execution_cost() {
        // Initialize an RNG.
        let rng = &mut TestRng::default();

        // Initialize a new caller.
        let caller_private_key = crate::vm::test_helpers::sample_genesis_private_key(rng);

        // Prepare the VM.
        let (vm, _) = prepare_vm(rng).unwrap();

        // Construct the base program.
        let base_program = Program::from_str(
            r"
program test_1.aleo;
mapping data:
    key as field.public;
    value as field.public;
function test:
    input r0 as field.public;
    input r1 as field.public;
    async test r0 r1 into r2;
    output r2 as test_1.aleo/test.future;
finalize test:
    input r0 as field.public;
    input r1 as field.public;
    hash.bhp256 r0 into r2 as field;
    hash.bhp256 r1 into r3 as field;
    set r2 into data[r3];",
        )
        .unwrap();

        // Deploy the program.
        let transaction = vm.deploy(&caller_private_key, &base_program, None, 0, None, rng).unwrap();

        // Construct the next block.
        let next_block = crate::test_helpers::sample_next_block(&vm, &caller_private_key, &[transaction], rng).unwrap();

        // Add the next block to the VM.
        vm.add_next_block(&next_block).unwrap();

        // Initialize programs up to the maximum depth.
        for i in 2..=Transaction::<CurrentNetwork>::MAX_TRANSITIONS - 1 {
            // Construct the program.
            let program = Program::from_str(&format!(
                r"
{imports}
program test_{curr}.aleo;
mapping data:
    key as field.public;
    value as field.public;
function test:
    input r0 as field.public;
    input r1 as field.public;
    call test_{prev}.aleo/test r0 r1 into r2;
    async test r0 r1 r2 into r3;
    output r3 as test_{curr}.aleo/test.future;
finalize test:
    input r0 as field.public;
    input r1 as field.public;
    input r2 as test_{prev}.aleo/test.future;
    await r2;
    hash.bhp256 r0 into r3 as field;
    hash.bhp256 r1 into r4 as field;
    set r3 into data[r4];",
                imports = (1..i).map(|j| format!("import test_{j}.aleo;")).join("\n"),
                prev = i - 1,
                curr = i,
            ))
            .unwrap();

            // Deploy the program.
            let transaction = vm.deploy(&caller_private_key, &program, None, 0, None, rng).unwrap();

            // Construct the next block.
            let next_block =
                crate::test_helpers::sample_next_block(&vm, &caller_private_key, &[transaction], rng).unwrap();

            // Add the next block to the VM.
            vm.add_next_block(&next_block).unwrap();
        }

        // Execute the program.
        let Transaction::Execute(_, execution, _) = vm
            .execute(
                &caller_private_key,
                (format!("test_{}.aleo", Transaction::<CurrentNetwork>::MAX_TRANSITIONS - 1), "test"),
                vec![Value::from_str("0field").unwrap(), Value::from_str("1field").unwrap()].iter(),
                None,
                0,
                None,
                rng,
            )
            .unwrap()
        else {
            unreachable!("VM::execute always produces an `Execution`")
        };

        // Check that the number of transitions is correct.
        assert_eq!(execution.transitions().len(), Transaction::<CurrentNetwork>::MAX_TRANSITIONS - 1);

        // Get the finalize cost of the execution.
        let (_, (_, finalize_cost)) = execution_cost(&vm.process().read(), &execution).unwrap();

        // Compute the expected cost as the sum of the cost in microcredits of each command in each finalize block of each transition in the execution.
        let mut expected_cost = 0;
        for transition in execution.transitions() {
            // Get the program ID and name of the transition.
            let program_id = transition.program_id();
            let function_name = transition.function_name();
            // Get the stack.
            let stack = vm.process().read().get_stack(program_id).unwrap().clone();
            // Get the finalize block of the transition and sum the cost of each command.
            let cost = match stack.get_function(function_name).unwrap().finalize_logic() {
                None => 0,
                Some(finalize_logic) => {
                    // Aggregate the cost of all commands in the program.
                    finalize_logic
                        .commands()
                        .iter()
                        .map(|command| cost_per_command(&stack, finalize_logic, command))
                        .try_fold(0u64, |acc, res| {
                            res.and_then(|x| acc.checked_add(x).ok_or(anyhow!("Finalize cost overflowed")))
                        })
                        .unwrap()
                }
            };
            // Add the cost to the total cost.
            expected_cost += cost;
        }

        // Check that the finalize cost is equal to the expected cost.
        assert_eq!(finalize_cost, expected_cost);
    }
}
