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
        deployment_or_execution_id: Field<N>,
        query: Option<Query<N, C::BlockStorage>>,
        rng: &mut R,
    ) -> Result<Transaction<N>> {
        // Compute the fee.
        let fee = self
            .execute_fee_raw(private_key, fee_record, fee_in_microcredits, deployment_or_execution_id, query, rng)?
            .1;
        // Return the fee transaction.
        Transaction::from_fee(fee)
    }

    /// Executes a fee for the given private key, fee record, and fee amount (in microcredits).
    /// Returns the response and fee.
    #[inline]
    pub fn execute_fee_raw<R: Rng + CryptoRng>(
        &self,
        private_key: &PrivateKey<N>,
        fee_record: Record<N, Plaintext<N>>,
        fee_in_microcredits: u64,
        deployment_or_execution_id: Field<N>,
        query: Option<Query<N, C::BlockStorage>>,
        rng: &mut R,
    ) -> Result<(Response<N>, Fee<N>)> {
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
                let deployment_or_execution_id = cast_ref!(deployment_or_execution_id as Field<$network>);
                lap!(timer, "Prepare the private key and fee record");

                // Execute the call to fee.
                let (response, _fee_transition, mut trace) = $process.execute_fee::<$aleo, _>(
                    private_key,
                    fee_record.clone(),
                    fee_in_microcredits,
                    *deployment_or_execution_id,
                    rng,
                )?;
                lap!(timer, "Execute the call to fee");

                // Prepare the assignments.
                cast_mut_ref!(trace as Trace<N>).prepare(query)?;
                lap!(timer, "Prepare the assignments");

                // Compute the proof and construct the fee.
                let trace = cast_ref!(trace as Trace<$network>);
                let fee = trace.prove_fee::<$aleo, _>(rng)?;
                lap!(timer, "Compute the proof and construct the fee");

                // Prepare the return.
                let response = cast_ref!(response as Response<N>).clone();
                let fee = cast_ref!(fee as Fee<N>).clone();
                lap!(timer, "Prepare the response and fee");

                finish!(timer);

                // Return the response and fee.
                Ok((response, fee))
            }};
        }
        // Process the logic.
        process!(self, logic)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fee_transition_size() {
        let rng = &mut TestRng::default();

        // Retrieve a fee transaction.
        let transaction = crate::vm::test_helpers::sample_fee_transaction(rng);
        // Retrieve the fee.
        let fee = match transaction {
            Transaction::Fee(_, fee) => fee,
            _ => panic!("Expected a fee transaction"),
        };
        // Assert the size of the transition.
        let fee_size_in_bytes = fee.to_bytes_le().unwrap().len();
        assert_eq!(1935, fee_size_in_bytes, "Update me if serialization has changed");
    }
}
