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
    /// Returns a new execute transaction.
    ///
    /// The `priority_fee_in_microcredits` is an additional fee **on top** of the deployment fee.
    pub fn execute<R: Rng + CryptoRng>(
        &self,
        private_key: &PrivateKey<N>,
        (program_id, function_name): (impl TryInto<ProgramID<N>>, impl TryInto<Identifier<N>>),
        inputs: impl ExactSizeIterator<Item = impl TryInto<Value<N>>>,
        fee: Option<(Record<N, Plaintext<N>>, u64)>,
        query: Option<Query<N, C::BlockStorage>>,
        rng: &mut R,
    ) -> Result<Transaction<N>> {
        // Compute the authorization.
        let authorization = self.authorize(private_key, program_id, function_name, inputs, rng)?;
        // Compute the execution.
        let (_response, execution) = self.execute_authorization_raw(authorization, query.clone(), rng)?;
        // Compute the fee.
        let fee = match fee {
            None => None,
            Some((credits, priority_fee_in_microcredits)) => {
                // Compute the minimum execution cost.
                let (minimum_execution_cost, (_, _)) = execution_cost(self, &execution)?;
                // Determine the fee.
                let fee_in_microcredits = minimum_execution_cost
                    .checked_add(priority_fee_in_microcredits)
                    .ok_or_else(|| anyhow!("Fee overflowed for an execution transaction"))?;
                // Compute the execution ID.
                let execution_id = execution.to_execution_id()?;
                // Compute the fee.
                Some(self.execute_fee_raw(private_key, credits, fee_in_microcredits, execution_id, query, rng)?.1)
            }
        };
        // Return the execute transaction.
        Transaction::from_execution(execution, fee)
    }

    /// Returns a new execute transaction for the given authorization.
    pub fn execute_authorization<R: Rng + CryptoRng>(
        &self,
        authorization: Authorization<N>,
        fee: Option<Fee<N>>,
        query: Option<Query<N, C::BlockStorage>>,
        rng: &mut R,
    ) -> Result<Transaction<N>> {
        // Compute the execution.
        let (_response, execution) = self.execute_authorization_raw(authorization, query, rng)?;
        // Return the execute transaction.
        Transaction::from_execution(execution, fee)
    }

    /// Executes a call to the program function for the given authorization.
    /// Returns the response and execution.
    #[inline]
    fn execute_authorization_raw<R: Rng + CryptoRng>(
        &self,
        authorization: Authorization<N>,
        query: Option<Query<N, C::BlockStorage>>,
        rng: &mut R,
    ) -> Result<(Response<N>, Execution<N>)> {
        let timer = timer!("VM::execute_authorization");

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

        // Compute the core logic.
        macro_rules! logic {
            ($process:expr, $network:path, $aleo:path) => {{
                // Prepare the authorization.
                let authorization = cast_ref!(authorization as Authorization<$network>);
                lap!(timer, "Prepare the authorization");

                // Execute the call.
                let (response, mut trace) = $process.execute::<$aleo>(authorization.clone())?;
                lap!(timer, "Execute the call");

                // Prepare the assignments.
                cast_mut_ref!(trace as Trace<N>).prepare(query)?;
                lap!(timer, "Prepare the assignments");

                // Compute the proof and construct the execution.
                let trace = cast_ref!(trace as Trace<$network>);
                let execution = trace.prove_execution::<$aleo, _>(&locator, rng)?;
                lap!(timer, "Compute the proof");

                // Prepare the return.
                let response = cast_ref!(response as Response<N>).clone();
                let execution = cast_ref!(execution as Execution<N>).clone();
                lap!(timer, "Prepare the response and execution");

                finish!(timer);

                // Return the response and execution.
                Ok((response, execution))
            }};
        }
        // Process the logic.
        process!(self, logic)
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
    fn test_mint_transaction_size() {
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
        let transaction = vm.execute(&caller_private_key, ("credits.aleo", "mint"), inputs, None, None, rng).unwrap();

        // Assert the size of the transaction.
        let transaction_size_in_bytes = transaction.to_bytes_le().unwrap().len();
        assert_eq!(1387, transaction_size_in_bytes, "Update me if serialization has changed");

        // Assert the size of the execution.
        assert!(matches!(transaction, Transaction::Execute(_, _, _)));
        if let Transaction::Execute(_, execution, _) = &transaction {
            let execution_size_in_bytes = execution.to_bytes_le().unwrap().len();
            assert_eq!(1352, execution_size_in_bytes, "Update me if serialization has changed");
        }
    }

    #[test]
    fn test_transfer_transaction_size() {
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
            vm.execute(&caller_private_key, ("credits.aleo", "transfer_private"), inputs, None, None, rng).unwrap();

        // Assert the size of the transaction.
        let transaction_size_in_bytes = transaction.to_bytes_le().unwrap().len();
        assert_eq!(2222, transaction_size_in_bytes, "Update me if serialization has changed");

        // Assert the size of the execution.
        assert!(matches!(transaction, Transaction::Execute(_, _, _)));
        if let Transaction::Execute(_, execution, _) = &transaction {
            let execution_size_in_bytes = execution.to_bytes_le().unwrap().len();
            assert_eq!(2187, execution_size_in_bytes, "Update me if serialization has changed");
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
        let transaction = vm.execute(&caller_private_key, ("credits.aleo", "join"), inputs, None, None, rng).unwrap();

        // Assert the size of the transaction.
        let transaction_size_in_bytes = transaction.to_bytes_le().unwrap().len();
        assert_eq!(2099, transaction_size_in_bytes, "Update me if serialization has changed");

        // Assert the size of the execution.
        assert!(matches!(transaction, Transaction::Execute(_, _, _)));
        if let Transaction::Execute(_, execution, _) = &transaction {
            let execution_size_in_bytes = execution.to_bytes_le().unwrap().len();
            assert_eq!(2064, execution_size_in_bytes, "Update me if serialization has changed");
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
        let transaction = vm.execute(&caller_private_key, ("credits.aleo", "split"), inputs, None, None, rng).unwrap();

        // Assert the size of the transaction.
        let transaction_size_in_bytes = transaction.to_bytes_le().unwrap().len();
        assert_eq!(2111, transaction_size_in_bytes, "Update me if serialization has changed");

        // Assert the size of the execution.
        assert!(matches!(transaction, Transaction::Execute(_, _, _)));
        if let Transaction::Execute(_, execution, _) = &transaction {
            let execution_size_in_bytes = execution.to_bytes_le().unwrap().len();
            assert_eq!(2076, execution_size_in_bytes, "Update me if serialization has changed");
        }
    }
}
