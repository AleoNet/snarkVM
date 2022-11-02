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
        rng: &mut R,
    ) -> Result<(Response<N>, Execution<N>)> {
        // Compute the core logic.
        macro_rules! logic {
            ($process:expr, $network:path, $aleo:path) => {{
                // Prepare the authorization.
                let authorization = cast_ref!(authorization as Authorization<$network>);

                // Execute the call.
                let (response, execution, inclusion) = $process.execute::<$aleo, _>(authorization.clone(), rng)?;

                // Prepare the assignments.
                let assignments = {
                    let execution = cast_ref!(execution as Execution<N>);
                    let inclusion = cast_ref!(inclusion as Inclusion<N>);
                    inclusion.prepare_execution(execution, self.block_store())?
                };
                let assignments = cast_ref!(assignments as Vec<InclusionAssignment<$network>>);

                // Compute the inclusion proof and update the execution.
                let execution = inclusion.prove_execution::<$aleo, _>(execution, assignments, rng)?;

                // Prepare the return.
                let response = cast_ref!(response as Response<N>).clone();
                let execution = cast_ref!(execution as Execution<N>).clone();
                // Return the response and execution.
                Ok((response, execution))
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
        rng: &mut R,
    ) -> Result<(Response<N>, Fee<N>)> {
        // Compute the core logic.
        macro_rules! logic {
            ($process:expr, $network:path, $aleo:path) => {{
                type RecordPlaintext<NetworkMacro> = Record<NetworkMacro, Plaintext<NetworkMacro>>;

                // Prepare the private key and credits record.
                let private_key = cast_ref!(&private_key as PrivateKey<$network>);
                let credits = cast_ref!(credits as RecordPlaintext<$network>);

                // Execute the call to fee.
                let (response, fee_transition, inclusion) =
                    $process.execute_fee::<$aleo, _>(private_key, credits.clone(), fee_in_gates, rng)?;

                // Prepare the assignments.
                let assignments = {
                    let fee_transition = cast_ref!(fee_transition as Transition<N>);
                    let inclusion = cast_ref!(inclusion as Inclusion<N>);
                    inclusion.prepare_fee(fee_transition, self.block_store())?
                };
                let assignments = cast_ref!(assignments as Vec<InclusionAssignment<$network>>);

                // Compute the inclusion proof and construct the fee.
                let fee = inclusion.prove_fee::<$aleo, _>(fee_transition, assignments, rng)?;

                // Prepare the return.
                let response = cast_ref!(response as Response<N>).clone();
                let fee = cast_ref!(fee as Fee<N>).clone();
                // Return the response and fee.
                Ok((response, fee))
            }};
        }
        // Process the logic.
        process!(self, logic)
    }
}
