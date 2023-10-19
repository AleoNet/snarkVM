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
                let (minimum_execution_cost, (_, _)) = execution_cost(self, &execution)?;
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
                let (_, mut trace) = $process.execute::<$aleo>(authorization.clone())?;
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
                let (_, mut trace) = $process.execute::<$aleo>(authorization.clone())?;
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
        network::Testnet3,
        program::{Ciphertext, Value},
        types::Field,
    };
    use ledger_block::Transition;
    use ledger_store::helpers::memory::ConsensusMemory;

    use indexmap::IndexMap;

    type CurrentNetwork = Testnet3;

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
        assert_eq!(3629, transaction_size_in_bytes, "Update me if serialization has changed");

        // Assert the size of the execution.
        assert!(matches!(transaction, Transaction::Execute(_, _, _)));
        if let Transaction::Execute(_, execution, _) = &transaction {
            let execution_size_in_bytes = execution.to_bytes_le().unwrap().len();
            assert_eq!(2210, execution_size_in_bytes, "Update me if serialization has changed");
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
        assert_eq!(2807, transaction_size_in_bytes, "Update me if serialization has changed");

        // Assert the size of the execution.
        assert!(matches!(transaction, Transaction::Execute(_, _, _)));
        if let Transaction::Execute(_, execution, _) = &transaction {
            let execution_size_in_bytes = execution.to_bytes_le().unwrap().len();
            assert_eq!(1388, execution_size_in_bytes, "Update me if serialization has changed");
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
        assert_eq!(3474, transaction_size_in_bytes, "Update me if serialization has changed");

        // Assert the size of the execution.
        assert!(matches!(transaction, Transaction::Execute(_, _, _)));
        if let Transaction::Execute(_, execution, _) = &transaction {
            let execution_size_in_bytes = execution.to_bytes_le().unwrap().len();
            assert_eq!(2055, execution_size_in_bytes, "Update me if serialization has changed");
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

        // Assert the size of the transaction.
        let transaction_size_in_bytes = transaction.to_bytes_le().unwrap().len();
        assert_eq!(2134, transaction_size_in_bytes, "Update me if serialization has changed");

        // Assert the size of the execution.
        assert!(matches!(transaction, Transaction::Execute(_, _, _)));
        if let Transaction::Execute(_, execution, _) = &transaction {
            let execution_size_in_bytes = execution.to_bytes_le().unwrap().len();
            assert_eq!(2099, execution_size_in_bytes, "Update me if serialization has changed");
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
        // Assert the size of the transition.
        let fee_size_in_bytes = fee.to_bytes_le().unwrap().len();
        assert_eq!(2011, fee_size_in_bytes, "Update me if serialization has changed");
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
        // Assert the size of the transition.
        let fee_size_in_bytes = fee.to_bytes_le().unwrap().len();
        assert_eq!(1384, fee_size_in_bytes, "Update me if serialization has changed");
    }
}
