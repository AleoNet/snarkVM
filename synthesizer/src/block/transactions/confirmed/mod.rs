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

use crate::{
    block::{Deployment, Execution, Transaction},
    stack::FinalizeOperation,
};
use console::network::prelude::*;

pub type NumFinalizeSize = u16;

/// A safety wrapper around a rejected type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Rejected<T: Clone + Debug + PartialEq + Eq + ToBytes>(pub T);

impl<T: Clone + Debug + PartialEq + Eq + ToBytes> Deref for Rejected<T> {
    type Target = T;

    /// Returns a reference to the rejected type.
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// The confirmed transaction.
#[derive(Clone, PartialEq, Eq)]
pub enum ConfirmedTransaction<N: Network> {
    /// The accepted deploy transaction is composed of `(index, deploy_transaction, finalize_operations)`.
    AcceptedDeploy(u32, Transaction<N>, Vec<FinalizeOperation<N>>),
    /// The accepted execute transaction is composed of `(index, execute_transaction, finalize_operations)`.
    AcceptedExecute(u32, Transaction<N>, Vec<FinalizeOperation<N>>),
    /// The rejected deploy transaction is composed of `(index, fee_transaction, rejected_deployment)`.
    RejectedDeploy(u32, Transaction<N>, Box<Rejected<Deployment<N>>>),
    /// The rejected execute transaction is composed of `(index, fee_transaction, rejected_execution)`.
    RejectedExecute(u32, Transaction<N>, Rejected<Execution<N>>),
}

impl<N: Network> ConfirmedTransaction<N> {
    /// Returns a new instance of an accepted deploy transaction.
    pub fn accepted_deploy(
        index: u32,
        transaction: Transaction<N>,
        finalize_operations: Vec<FinalizeOperation<N>>,
    ) -> Result<Self> {
        // Retrieve the program from the deployment, and ensure the transaction is a deploy transaction.
        let program = match &transaction {
            Transaction::Deploy(_, _, deployment, _) => deployment.program(),
            Transaction::Execute(..) | Transaction::Fee(..) => {
                bail!("Transaction '{}' is not a deploy transaction", transaction.id())
            }
        };
        // Ensure the number of program mappings matches the number of finalize operations.
        if program.mappings().len() != finalize_operations.len() {
            bail!(
                "The number of program mappings ({}) does not match the nubmer of finalize operations ({})",
                program.mappings().len(),
                finalize_operations.len()
            )
        }
        // Ensure the finalize operations contain the correct types.
        for operation in finalize_operations.iter() {
            // Ensure the finalize operation is an initialize mapping.
            if !matches!(operation, FinalizeOperation::InitializeMapping(..)) {
                bail!("Transaction '{}' (deploy) contains an invalid finalize operation type", transaction.id())
            }
        }
        // Return the accepted deploy transaction.
        Ok(Self::AcceptedDeploy(index, transaction, finalize_operations))
    }

    /// Returns a new instance of an accepted execute transaction.
    pub fn accepted_execute(
        index: u32,
        transaction: Transaction<N>,
        finalize_operations: Vec<FinalizeOperation<N>>,
    ) -> Result<Self> {
        // Ensure the finalize operations contain the correct types.
        for operation in finalize_operations.iter() {
            // Ensure the finalize operation is an insert or update key-value operation.
            match operation {
                FinalizeOperation::InsertKeyValue(..) | FinalizeOperation::UpdateKeyValue(..) => (),
                FinalizeOperation::InitializeMapping(..)
                | FinalizeOperation::RemoveMapping(..)
                | FinalizeOperation::RemoveKeyValue(..) => {
                    bail!("Transaction '{}' (execute) contains an invalid finalize operation type", transaction.id())
                }
            }
        }
        // Ensure the transaction is an execute transaction.
        match transaction.is_execute() {
            true => Ok(Self::AcceptedExecute(index, transaction, finalize_operations)),
            false => bail!("Transaction '{}' is not an execute transaction", transaction.id()),
        }
    }

    /// Returns a new instance of a rejected deploy transaction.
    pub fn rejected_deploy(
        index: u32,
        transaction: Transaction<N>,
        rejected_deployment: Deployment<N>,
    ) -> Result<Self> {
        // Ensure the transaction is a fee transaction.
        match transaction.is_fee() {
            true => Ok(Self::RejectedDeploy(index, transaction, Box::new(Rejected(rejected_deployment)))),
            false => bail!("Transaction '{}' is not a fee transaction", transaction.id()),
        }
    }

    /// Returns a new instance of a rejected execute transaction.
    pub fn rejected_execute(index: u32, transaction: Transaction<N>, rejected_execution: Execution<N>) -> Result<Self> {
        // Ensure the transaction is a fee transaction.
        match transaction.is_fee() {
            true => Ok(Self::RejectedExecute(index, transaction, Rejected(rejected_execution))),
            false => bail!("Transaction '{}' is not a fee transaction", transaction.id()),
        }
    }
}

impl<N: Network> ConfirmedTransaction<N> {
    /// Returns 'true' if the confirmed transaction is accepted.
    pub fn is_accepted(&self) -> bool {
        match self {
            Self::AcceptedDeploy(..) | Self::AcceptedExecute(..) => true,
            Self::RejectedDeploy(..) | Self::RejectedExecute(..) => false,
        }
    }

    /// Returns 'true' if the confirmed transaction is rejected.
    pub fn is_rejected(&self) -> bool {
        !self.is_accepted()
    }
}

impl<N: Network> ConfirmedTransaction<N> {
    /// Returns the confirmed transaction index.
    pub fn index(&self) -> u32 {
        match self {
            Self::AcceptedDeploy(index, ..) => *index,
            Self::AcceptedExecute(index, ..) => *index,
            Self::RejectedDeploy(index, ..) => *index,
            Self::RejectedExecute(index, ..) => *index,
        }
    }

    /// Returns the transaction.
    pub fn transaction(&self) -> &Transaction<N> {
        match self {
            Self::AcceptedDeploy(_, transaction, _) => transaction,
            Self::AcceptedExecute(_, transaction, _) => transaction,
            Self::RejectedDeploy(_, transaction, _) => transaction,
            Self::RejectedExecute(_, transaction, _) => transaction,
        }
    }

    /// Returns the transaction.
    pub fn into_transaction(self) -> Transaction<N> {
        match self {
            Self::AcceptedDeploy(_, transaction, _) => transaction,
            Self::AcceptedExecute(_, transaction, _) => transaction,
            Self::RejectedDeploy(_, transaction, _) => transaction,
            Self::RejectedExecute(_, transaction, _) => transaction,
        }
    }

    /// Returns the number of finalize operations.
    pub fn num_finalize(&self) -> usize {
        match self {
            Self::AcceptedDeploy(_, _, finalize) | Self::AcceptedExecute(_, _, finalize) => finalize.len(),
            Self::RejectedDeploy(..) | Self::RejectedExecute(..) => 0,
        }
    }

    /// Returns the finalize operations for the confirmed transaction.
    pub fn finalize_operations(&self) -> Option<&Vec<FinalizeOperation<N>>> {
        match self {
            Self::AcceptedDeploy(_, _, finalize) => Some(finalize),
            Self::AcceptedExecute(_, _, finalize) => Some(finalize),
            Self::RejectedDeploy(..) | Self::RejectedExecute(..) => None,
        }
    }
}

impl<N: Network> Deref for ConfirmedTransaction<N> {
    type Target = Transaction<N>;

    /// Returns a reference to the valid transaction.
    fn deref(&self) -> &Self::Target {
        self.transaction()
    }
}

#[cfg(test)]
pub(crate) mod test_helpers {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    /// Samples an accepted deploy transaction at the given index.
    pub(crate) fn sample_accepted_deploy(index: u32, rng: &mut TestRng) -> ConfirmedTransaction<CurrentNetwork> {
        // Sample a deploy transaction.
        let tx = crate::vm::test_helpers::sample_deployment_transaction(rng);
        // Return the confirmed transaction.
        ConfirmedTransaction::accepted_deploy(index, tx, vec![FinalizeOperation::InitializeMapping(Uniform::rand(rng))])
            .unwrap()
    }

    /// Samples an accepted execute transaction at the given index.
    pub(crate) fn sample_accepted_execute(index: u32, rng: &mut TestRng) -> ConfirmedTransaction<CurrentNetwork> {
        // Sample an execute transaction.
        let tx = crate::vm::test_helpers::sample_execution_transaction_with_fee(rng);
        // Return the confirmed transaction.
        ConfirmedTransaction::accepted_execute(index, tx, vec![]).unwrap()
    }

    /// Samples a rejected deploy transaction at the given index.
    pub(crate) fn sample_rejected_deploy(index: u32, rng: &mut TestRng) -> ConfirmedTransaction<CurrentNetwork> {
        // Sample a fee transaction.
        let fee_transaction = crate::vm::test_helpers::sample_fee_transaction(rng);

        // Extract the deployment.
        let deploy = match crate::vm::test_helpers::sample_deployment_transaction(rng) {
            Transaction::Deploy(_, _, deploy, _) => (*deploy).clone(),
            _ => unreachable!(),
        };

        // Return the confirmed transaction.
        ConfirmedTransaction::rejected_deploy(index, fee_transaction, deploy).unwrap()
    }

    /// Samples a rejected execute transaction at the given index.
    pub(crate) fn sample_rejected_execute(index: u32, rng: &mut TestRng) -> ConfirmedTransaction<CurrentNetwork> {
        // Sample a fee transaction.
        let fee_transaction = crate::vm::test_helpers::sample_fee_transaction(rng);

        // Extract the execution.
        let execute = match crate::vm::test_helpers::sample_execution_transaction_with_fee(rng) {
            Transaction::Execute(_, execute, _) => execute,
            _ => unreachable!(),
        };

        // Return the confirmed transaction.
        ConfirmedTransaction::rejected_execute(index, fee_transaction, execute).unwrap()
    }

    /// Sample a list of randomly confirmed transactions.
    pub(crate) fn sample_confirmed_transactions() -> Vec<ConfirmedTransaction<CurrentNetwork>> {
        let rng = &mut TestRng::default();

        vec![
            sample_accepted_deploy(0, rng),
            sample_accepted_execute(1, rng),
            sample_rejected_deploy(2, rng),
            sample_rejected_execute(3, rng),
            sample_accepted_deploy(Uniform::rand(rng), rng),
            sample_accepted_execute(Uniform::rand(rng), rng),
            sample_rejected_deploy(Uniform::rand(rng), rng),
            sample_rejected_execute(Uniform::rand(rng), rng),
        ]
    }
}
