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

mod bytes;
mod serialize;
mod string;

use super::*;

use crate::block::{Deployment, Execution};

/// A wrapper around the rejected deployment or execution.
#[derive(Clone, PartialEq, Eq)]
pub enum Rejected<N: Network> {
    Deployment(ProgramOwner<N>, Box<Deployment<N>>),
    Execution(Execution<N>),
}

impl<N: Network> Rejected<N> {
    /// Initializes a rejected deployment.
    pub fn new_deployment(program_owner: ProgramOwner<N>, deployment: Deployment<N>) -> Self {
        Self::Deployment(program_owner, Box::new(deployment))
    }

    /// Initializes a rejected execution.
    pub fn new_execution(execution: Execution<N>) -> Self {
        Self::Execution(execution)
    }

    /// Returns true if the rejected transaction is a deployment.
    pub fn is_deployment(&self) -> bool {
        matches!(self, Self::Deployment(..))
    }

    /// Returns true if the rejected transaction is an execution.
    pub fn is_execution(&self) -> bool {
        matches!(self, Self::Execution(..))
    }

    /// Returns the program owner of the rejected deployment.
    pub fn program_owner(&self) -> Result<&ProgramOwner<N>> {
        match self {
            Self::Deployment(program_owner, _) => Ok(program_owner),
            _ => bail!("Rejected transaction is not a deployment"),
        }
    }

    /// Returns the rejected deployment.
    pub fn deployment(&self) -> Result<&Deployment<N>> {
        match self {
            Self::Deployment(_, deployment) => Ok(deployment),
            _ => bail!("Rejected transaction is not a deployment"),
        }
    }

    /// Returns the rejected execution.
    pub fn execution(&self) -> Result<&Execution<N>> {
        match self {
            Self::Execution(execution) => Ok(execution),
            _ => bail!("Rejected transaction is not an execution"),
        }
    }

    /// Returns the rejected ID.
    pub fn to_id(&self) -> Result<Field<N>> {
        match self {
            Self::Deployment(_, deployment) => deployment.to_deployment_id(),
            Self::Execution(execution) => execution.to_execution_id(),
        }
    }
}

#[cfg(test)]
pub(crate) mod test_helpers {
    use super::*;
    use console::{account::PrivateKey, network::Testnet3};

    type CurrentNetwork = Testnet3;

    /// Samples a rejected deployment.
    pub(crate) fn sample_rejected_deployment(rng: &mut TestRng) -> Rejected<CurrentNetwork> {
        // Sample a deploy transaction.
        let deployment = match crate::vm::test_helpers::sample_deployment_transaction(rng) {
            Transaction::Deploy(_, _, deployment, _) => (*deployment).clone(),
            _ => unreachable!(),
        };

        // Sample a new program owner.
        let private_key = PrivateKey::new(rng).unwrap();
        let deployment_id = deployment.to_deployment_id().unwrap();
        let program_owner = ProgramOwner::new(&private_key, deployment_id, rng).unwrap();

        // Return the rejected deployment.
        Rejected::new_deployment(program_owner, deployment)
    }

    /// Samples a rejected execution.
    pub(crate) fn sample_rejected_execution(rng: &mut TestRng) -> Rejected<CurrentNetwork> {
        // Sample an execute transaction.
        let execution = match crate::vm::test_helpers::sample_execution_transaction_with_fee(rng) {
            Transaction::Execute(_, execution, _) => execution,
            _ => unreachable!(),
        };

        // Return the rejected execution.
        Rejected::new_execution(execution)
    }

    /// Sample a list of randomly rejected transactions.
    pub(crate) fn sample_rejected_transactions() -> Vec<Rejected<CurrentNetwork>> {
        let rng = &mut TestRng::default();

        vec![sample_rejected_deployment(rng), sample_rejected_execution(rng)]
    }
}
