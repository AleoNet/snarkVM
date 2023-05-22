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

impl<N: Network, C: ConsensusStorage<N>> VM<N, C> {
    /// Returns a new deploy transaction.
    ///
    /// The `priority_fee_in_microcredits` is an additional fee **on top** of the deployment fee.
    pub fn deploy<R: Rng + CryptoRng>(
        &self,
        private_key: &PrivateKey<N>,
        program: &Program<N>,
        (fee_record, priority_fee_in_microcredits): (Record<N, Plaintext<N>>, u64),
        query: Option<Query<N, C::BlockStorage>>,
        rng: &mut R,
    ) -> Result<Transaction<N>> {
        // Compute the deployment.
        let deployment = self.deploy_raw(program, rng)?;
        // Ensure the transaction is not empty.
        ensure!(!deployment.program().functions().is_empty(), "Attempted to create an empty transaction deployment");

        // Determine the fee.
        let fee_in_microcredits = deployment
            .size_in_bytes()?
            .checked_mul(N::DEPLOYMENT_FEE_MULTIPLIER)
            .and_then(|deployment_fee| deployment_fee.checked_add(priority_fee_in_microcredits))
            .ok_or_else(|| anyhow!("Fee overflowed for a deployment transaction"))?;

        // Compute the fee.
        let (_, fee, _) = self.execute_fee_raw(private_key, fee_record, fee_in_microcredits, query, rng)?;

        // Construct the owner.
        let id = *Transaction::deployment_tree(&deployment, &fee)?.root();
        let owner = ProgramOwner::new(private_key, id.into(), rng)?;

        // Return the deploy transaction.
        Transaction::from_deployment(owner, deployment, fee)
    }

    /// Returns a deployment for the given program.
    #[inline]
    pub fn deploy_raw<R: Rng + CryptoRng>(&self, program: &Program<N>, rng: &mut R) -> Result<Deployment<N>> {
        let timer = timer!("VM::deploy_raw");

        // Compute the core logic.
        macro_rules! logic {
            ($process:expr, $network:path, $aleo:path) => {{
                // Prepare the program.
                let program = cast_ref!(&program as Program<$network>);

                // Compute the deployment.
                let deployment = $process.deploy::<$aleo, _>(program, rng)?;
                lap!(timer, "Compute the deployment");

                // Prepare the return.
                let deployment = cast_ref!(deployment as Deployment<N>).clone();
                lap!(timer, "Prepare the deployment");

                finish!(timer);
                // Return the deployment.
                Ok(deployment)
            }};
        }
        // Process the logic.
        process!(self, logic)
    }
}
