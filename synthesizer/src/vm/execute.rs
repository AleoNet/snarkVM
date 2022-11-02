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
        // Fetch the block store.
        let block_store = self.block_store();
        // Compute the core logic.
        macro_rules! logic {
            ($process:expr, $network:path, $aleo:path) => {{
                // Prepare the authorization and block store.
                let authorization = cast_ref!(authorization as Authorization<$network>);
                let block_store = cast_ref!(block_store as BlockStore<$network, C::BlockStorage>);

                // Execute the call.
                let (response, execution, inclusion) = $process.execute::<$aleo, _>(authorization.clone(), rng)?;
                // Compute the inclusion proof and update the execution.
                let execution = inclusion.prove_execution::<$aleo, _, _>(&execution, &block_store, rng)?;

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
        // Fetch the block store.
        let block_store = self.block_store();
        // Compute the core logic.
        macro_rules! logic {
            ($process:expr, $network:path, $aleo:path) => {{
                type RecordPlaintext<NetworkMacro> = Record<NetworkMacro, Plaintext<NetworkMacro>>;

                // Prepare the private key, credits record, and block store.
                let private_key = cast_ref!(&private_key as PrivateKey<$network>);
                let credits = cast_ref!(credits as RecordPlaintext<$network>);
                let block_store = cast_ref!(block_store as BlockStore<$network, C::BlockStorage>);

                // Execute the call to fee.
                let (response, fee_transition, inclusion) =
                    $process.execute_fee::<$aleo, _>(private_key, credits.clone(), fee_in_gates, rng)?;
                // Compute the inclusion proof and update the execution.
                let fee = inclusion.prove_fee::<$aleo, _, _>(&fee_transition, &block_store, rng)?;

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
