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

        // Compute the minimum deployment cost.
        let (minimum_deployment_cost, (_, _)) = deployment_cost(&deployment)?;
        // Determine the fee.
        let fee_in_microcredits = minimum_deployment_cost
            .checked_add(priority_fee_in_microcredits)
            .ok_or_else(|| anyhow!("Fee overflowed for a deployment transaction"))?;

        // Compute the deployment ID.
        let deployment_id = deployment.to_deployment_id()?;

        // Compute the fee.
        let (_, fee) = self.execute_fee_raw(private_key, fee_record, fee_in_microcredits, deployment_id, query, rng)?;

        // Construct the owner.
        let owner = ProgramOwner::new(private_key, deployment_id, rng)?;

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
