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
    // TODO (raychu86): DO NOT CONSTRUCT THIS FROM SCRATCH. This is incredibly inefficient.
    //  This should be done by passing in the block tree or cacheing it in the VM.
    /// Returns the current block tree of the ledger.
    pub fn block_tree(&self) -> Result<BlockTree<N>> {
        // Construct the block tree.
        let mut block_tree: BlockTree<N> = N::merkle_tree_bhp(&[])?;

        let block_store = self.block_store();
        let latest_height = *block_store.heights().max().unwrap_or(Cow::Owned(0));

        if block_store.get_block_hash(0)?.is_some() {
            let hashes: Result<Vec<_>> = (0..=latest_height)
                .map(|height| {
                    block_store.get_block_hash(height).map(|hash| {
                        hash.ok_or_else(|| anyhow!("Failed to load block hash at height {}", height))
                            .map(|x| x.to_bits_le())
                    })
                })
                .try_collect()?;
            block_tree.append(&hashes?)?;
        }

        Ok(block_tree)
    }

    /// Executes a call to the program function for the given inputs.
    #[inline]
    pub fn execute<R: Rng + CryptoRng>(
        &self,
        authorization: Authorization<N>,
        rng: &mut R,
    ) -> Result<(Response<N>, Execution<N>)> {
        // Construct the block tree.
        let block_tree: BlockTree<N> = self.block_tree()?;

        // Fetch the block storage.
        let block_store = self.block_store();

        // Add the required state paths to the authorization
        let mut authorization = authorization;
        for input_id in authorization.to_vec_deque().iter().flat_map(|request| request.input_ids()) {
            // Generate the relevant state roots for each input record.
            if let InputID::Record(commitment, ..) = input_id {
                let state_path = StatePath::new_commitment(&block_tree, block_store, commitment)?;
                authorization.insert_state_path(*commitment, state_path);
            }
        }

        // Compute the core logic.
        macro_rules! logic {
            ($process:expr, $network:path, $aleo:path) => {{
                // Prepare the authorization.
                let authorization = cast_ref!(authorization as Authorization<$network>);

                // Execute the call.
                let (response, execution) = $process.execute::<$aleo, _>(authorization.clone(), rng)?;

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

    /// Returns an additional fee for the given private key, credits record, and additional fee amount (in gates).
    #[inline]
    pub fn execute_additional_fee<R: Rng + CryptoRng>(
        &self,
        private_key: &PrivateKey<N>,
        credits: Record<N, Plaintext<N>>,
        additional_fee_in_gates: u64,
        rng: &mut R,
    ) -> Result<(Response<N>, AdditionalFee<N>)> {
        // Generate the state path for the given credits record.
        let state_path = {
            let block_tree = self.block_tree()?;

            // Fetch the block storage.
            let block_store = self.block_store();

            // Ensure the additional fee has the correct program ID.
            let program_id = ProgramID::from_str("credits.aleo")?;
            // Ensure the additional fee has the correct function.
            let function_name = Identifier::from_str("fee")?;

            let input_types = self.process.read().get_program(&program_id)?.get_function(&function_name)?.input_types();

            match input_types[0] {
                ValueType::Record(record_name) => {
                    let commitment = credits.to_commitment(
                        cast_ref!(program_id as ProgramID<N>),
                        cast_ref!(record_name as Identifier<N>),
                    )?;
                    StatePath::new_commitment(&block_tree, block_store, &commitment)?
                }
                _ => bail!("Invalid input type"),
            }
        };

        // Compute the core logic.
        macro_rules! logic {
            ($process:expr, $network:path, $aleo:path) => {{
                type RecordPlaintext<NetworkMacro> = Record<NetworkMacro, Plaintext<NetworkMacro>>;

                // Prepare the private key and credits record.
                let private_key = cast_ref!(&private_key as PrivateKey<$network>);
                let credits = cast_ref!(credits as RecordPlaintext<$network>);
                let state_path = cast_ref!(state_path as StatePath<$network>);

                // Execute the call to additional fee.
                let (response, additional_fee) = $process.execute_additional_fee::<$aleo, _>(
                    private_key,
                    credits.clone(),
                    state_path.clone(),
                    additional_fee_in_gates,
                    rng,
                )?;

                // Prepare the return.
                let response = cast_ref!(response as Response<N>).clone();
                let additional_fee = cast_ref!(additional_fee as AdditionalFee<N>).clone();
                // Return the response and additional fee.
                Ok((response, additional_fee))
            }};
        }
        // Process the logic.
        process!(self, logic)
    }
}
