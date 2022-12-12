// Copyright (C) 2019-2022 Aleo Systems Inc.
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

impl<N: Network, C: ConsensusStorage<N>> VM<N, C> {
    /// Executes a call to the program function for the given inputs.
    #[inline]
    pub fn execute<R: Rng + CryptoRng>(
        &self,
        authorization: Authorization<N>,
        query: Option<Query<N, C::BlockStorage>>,
        rng: &mut R,
    ) -> Result<(Response<N>, Execution<N>, Vec<CallMetrics<N>>)> {
        let timer = timer!("VM::execute");

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
                let (response, execution, inclusion, metrics) =
                    $process.execute::<$aleo, _>(authorization.clone(), rng)?;
                lap!(timer, "Execute the call");

                // Prepare the assignments.
                let (assignments, global_state_root) = {
                    let execution = cast_ref!(execution as Execution<N>);
                    let inclusion = cast_ref!(inclusion as Inclusion<N>);
                    inclusion.prepare_execution(execution, query)?
                };
                let assignments = cast_ref!(assignments as Vec<InclusionAssignment<$network>>);
                let global_state_root = *cast_ref!((*global_state_root) as Field<$network>);

                lap!(timer, "Prepare the assignments");

                // Compute the inclusion proof and update the execution.
                let execution =
                    inclusion.prove_execution::<$aleo, _>(execution, assignments, global_state_root.into(), rng)?;
                lap!(timer, "Compute the inclusion proof");

                // Prepare the return.
                let response = cast_ref!(response as Response<N>).clone();
                let execution = cast_ref!(execution as Execution<N>).clone();
                let metrics = cast_ref!(metrics as Vec<CallMetrics<N>>).clone();
                lap!(timer, "Prepare the response and execution");

                finish!(timer);

                // Return the response, execution, and metrics.
                Ok((response, execution, metrics))
            }};
        }
        // Process the logic.
        process!(self, logic)
    }

    /// Executes a fee for the given private key, credits record, and fee amount (in gates).
    #[inline]
    pub fn execute_fee<R: Rng + CryptoRng>(
        &self,
        private_key: &PrivateKey<N>,
        credits: Record<N, Plaintext<N>>,
        fee_in_gates: u64,
        query: Option<Query<N, C::BlockStorage>>,
        rng: &mut R,
    ) -> Result<(Response<N>, Fee<N>, Vec<CallMetrics<N>>)> {
        let timer = timer!("VM::execute_fee");

        // Prepare the query.
        let query = match query {
            Some(query) => query,
            None => Query::VM(self.block_store().clone()),
        };
        lap!(timer, "Prepare the query");

        // Compute the core logic.
        macro_rules! logic {
            ($process:expr, $network:path, $aleo:path) => {{
                type RecordPlaintext<NetworkMacro> = Record<NetworkMacro, Plaintext<NetworkMacro>>;

                // Prepare the private key and credits record.
                let private_key = cast_ref!(&private_key as PrivateKey<$network>);
                let credits = cast_ref!(credits as RecordPlaintext<$network>);
                lap!(timer, "Prepare the private key and credits record");

                // Execute the call to fee.
                let (response, fee_transition, inclusion, metrics) =
                    $process.execute_fee::<$aleo, _>(private_key, credits.clone(), fee_in_gates, rng)?;
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
