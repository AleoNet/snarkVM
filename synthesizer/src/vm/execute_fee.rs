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
    /// Executes a fee for the given private key, fee record, and fee amount (in microcredits).
    /// Returns the fee transaction.
    #[inline]
    pub fn execute_fee<R: Rng + CryptoRng>(
        &self,
        private_key: &PrivateKey<N>,
        fee_record: Record<N, Plaintext<N>>,
        fee_in_microcredits: u64,
        query: Option<Query<N, C::BlockStorage>>,
        rng: &mut R,
    ) -> Result<Transaction<N>> {
        // Compute the fee.
        let fee = self.execute_fee_raw(private_key, fee_record, fee_in_microcredits, query, rng)?.1;
        // Return the fee transaction.
        Transaction::from_fee(fee)
    }

    /// Executes a fee for the given private key, fee record, and fee amount (in microcredits).
    /// Returns the response, fee, and call metrics.
    #[inline]
    pub fn execute_fee_raw<R: Rng + CryptoRng>(
        &self,
        private_key: &PrivateKey<N>,
        fee_record: Record<N, Plaintext<N>>,
        fee_in_microcredits: u64,
        query: Option<Query<N, C::BlockStorage>>,
        rng: &mut R,
    ) -> Result<(Response<N>, Fee<N>, Vec<CallMetrics<N>>)> {
        let timer = timer!("VM::execute_fee_raw");

        // Prepare the query.
        let query = match query {
            Some(query) => query,
            None => Query::VM(self.block_store().clone()),
        };
        lap!(timer, "Prepare the query");

        // TODO (raychu86): Ensure that the fee record is associated with the `credits.aleo` program
        // Ensure that the record has enough balance to pay the fee.
        match fee_record.find(&[Identifier::from_str("microcredits")?]) {
            Ok(Entry::Private(Plaintext::Literal(Literal::U64(amount), _))) => {
                if *amount < fee_in_microcredits {
                    bail!("Fee record does not have enough balance to pay the fee")
                }
            }
            _ => bail!("Fee record does not have microcredits"),
        }

        // Compute the core logic.
        macro_rules! logic {
            ($process:expr, $network:path, $aleo:path) => {{
                type RecordPlaintext<NetworkMacro> = Record<NetworkMacro, Plaintext<NetworkMacro>>;

                // Prepare the private key and fee record.
                let private_key = cast_ref!(&private_key as PrivateKey<$network>);
                let fee_record = cast_ref!(fee_record as RecordPlaintext<$network>);
                lap!(timer, "Prepare the private key and fee record");

                // Execute the call to fee.
                let (response, fee_transition, inclusion, metrics) =
                    $process.execute_fee::<$aleo, _>(private_key, fee_record.clone(), fee_in_microcredits, rng)?;
                lap!(timer, "Execute the call to fee");

                // Prepare the assignments.
                let assignments = {
                    let fee_transition = cast_ref!(fee_transition as Transition<N>);
                    let inclusion = cast_ref!(inclusion as Inclusion<N>);
                    inclusion.prepare_fee(fee_transition, query)?
                };
                let assignments = cast_ref!(assignments as Vec<InclusionAssignment<$network>>);
                lap!(timer, "Prepare the assignments");

                // Compute the inclusion proof and construct the fee.
                let fee = inclusion.prove_fee::<$aleo, _>(fee_transition, assignments, rng)?;
                lap!(timer, "Compute the inclusion proof and construct the fee");

                // Prepare the return.
                let response = cast_ref!(response as Response<N>).clone();
                let fee = cast_ref!(fee as Fee<N>).clone();
                let metrics = cast_ref!(metrics as Vec<CallMetrics<N>>).clone();
                lap!(timer, "Prepare the response, fee, and metrics");

                finish!(timer);

                // Return the response, fee, metrics.
                Ok((response, fee, metrics))
            }};
        }
        // Process the logic.
        process!(self, logic)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::store::helpers::memory::ConsensusMemory;
    use console::{account::ViewKey, network::Testnet3, program::Ciphertext};

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
    fn test_fee_transition_size() {
        let rng = &mut TestRng::default();

        // Initialize a new caller.
        let caller_private_key = crate::vm::test_helpers::sample_genesis_private_key(rng);
        let caller_view_key = ViewKey::try_from(&caller_private_key).unwrap();

        // Prepare the VM and records.
        let (vm, records) = prepare_vm(rng).unwrap();

        // Fetch the unspent record.
        let record = records.values().next().unwrap().decrypt(&caller_view_key).unwrap();

        // Execute.
        let (_, fee, _) = vm.execute_fee_raw(&caller_private_key, record, 1, None, rng).unwrap();

        // Assert the size of the transition.
        let fee_size_in_bytes = fee.to_bytes_le().unwrap().len();
        assert_eq!(2247, fee_size_in_bytes, "Update me if serialization has changed");
    }
}
