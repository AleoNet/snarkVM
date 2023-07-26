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

use crate::{rejected::Rejected, Transaction};
use console::network::prelude::*;
use synthesizer_program::FinalizeOperation;

pub type NumFinalizeSize = u16;

/// The confirmed transaction.
#[derive(Clone, PartialEq, Eq)]
pub enum ConfirmedTransaction<N: Network> {
    /// The accepted deploy transaction is composed of `(index, deploy_transaction, finalize_operations)`.
    AcceptedDeploy(u32, Transaction<N>, Vec<FinalizeOperation<N>>),
    /// The accepted execute transaction is composed of `(index, execute_transaction, finalize_operations)`.
    AcceptedExecute(u32, Transaction<N>, Vec<FinalizeOperation<N>>),
    /// The rejected deploy transaction is composed of `(index, fee_transaction, rejected_deployment)`.
    RejectedDeploy(u32, Transaction<N>, Rejected<N>),
    /// The rejected execute transaction is composed of `(index, fee_transaction, rejected_execution)`.
    RejectedExecute(u32, Transaction<N>, Rejected<N>),
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
                "The number of program mappings ({}) does not match the number of finalize operations ({})",
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
                FinalizeOperation::InsertKeyValue(..)
                | FinalizeOperation::UpdateKeyValue(..)
                | FinalizeOperation::RemoveKeyValue(..) => (),
                FinalizeOperation::InitializeMapping(..) | FinalizeOperation::RemoveMapping(..) => {
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
    pub fn rejected_deploy(index: u32, transaction: Transaction<N>, rejected: Rejected<N>) -> Result<Self> {
        ensure!(rejected.is_deployment(), "Rejected deployment is not a deployment");

        // Ensure the transaction is a fee transaction.
        match transaction.is_fee() {
            true => Ok(Self::RejectedDeploy(index, transaction, rejected)),
            false => bail!("Transaction '{}' is not a fee transaction", transaction.id()),
        }
    }

    /// Returns a new instance of a rejected execute transaction.
    pub fn rejected_execute(index: u32, transaction: Transaction<N>, rejected: Rejected<N>) -> Result<Self> {
        ensure!(rejected.is_execution(), "Rejected execution is not an execution");

        // Ensure the transaction is a fee transaction.
        match transaction.is_fee() {
            true => Ok(Self::RejectedExecute(index, transaction, rejected)),
            false => bail!("Transaction '{}' is not a fee transaction", transaction.id()),
        }
    }
}

impl<N: Network> ConfirmedTransaction<N> {
    /// Returns 'true' if the confirmed transaction is accepted.
    pub const fn is_accepted(&self) -> bool {
        match self {
            Self::AcceptedDeploy(..) | Self::AcceptedExecute(..) => true,
            Self::RejectedDeploy(..) | Self::RejectedExecute(..) => false,
        }
    }

    /// Returns 'true' if the confirmed transaction is rejected.
    pub const fn is_rejected(&self) -> bool {
        !self.is_accepted()
    }
}

impl<N: Network> ConfirmedTransaction<N> {
    /// Returns the confirmed transaction index.
    pub const fn index(&self) -> u32 {
        match self {
            Self::AcceptedDeploy(index, ..) => *index,
            Self::AcceptedExecute(index, ..) => *index,
            Self::RejectedDeploy(index, ..) => *index,
            Self::RejectedExecute(index, ..) => *index,
        }
    }

    /// Returns the human-readable variant of the confirmed transaction.
    pub const fn variant(&self) -> &str {
        match self {
            Self::AcceptedDeploy(..) => "accepted deploy",
            Self::AcceptedExecute(..) => "accepted execute",
            Self::RejectedDeploy(..) => "rejected deploy",
            Self::RejectedExecute(..) => "rejected execute",
        }
    }

    /// Returns the transaction.
    pub const fn transaction(&self) -> &Transaction<N> {
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
    pub const fn finalize_operations(&self) -> Option<&Vec<FinalizeOperation<N>>> {
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
pub mod test_helpers {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    /// Samples an accepted deploy transaction at the given index.
    pub(crate) fn sample_accepted_deploy(index: u32, rng: &mut TestRng) -> ConfirmedTransaction<CurrentNetwork> {
        // Sample a deploy transaction.
        let tx = crate::transaction::test_helpers::sample_deployment_transaction(rng);
        // Return the confirmed transaction.
        ConfirmedTransaction::accepted_deploy(index, tx, vec![FinalizeOperation::InitializeMapping(Uniform::rand(rng))])
            .unwrap()
    }

    /// Samples an accepted execute transaction at the given index.
    pub(crate) fn sample_accepted_execute(index: u32, rng: &mut TestRng) -> ConfirmedTransaction<CurrentNetwork> {
        // Sample an execute transaction.
        let tx = crate::transaction::test_helpers::sample_execution_transaction_with_fee(rng);
        // Return the confirmed transaction.
        ConfirmedTransaction::accepted_execute(index, tx, vec![]).unwrap()
    }

    /// Samples a rejected deploy transaction at the given index.
    pub(crate) fn sample_rejected_deploy(index: u32, rng: &mut TestRng) -> ConfirmedTransaction<CurrentNetwork> {
        // Sample a fee transaction.
        let fee_transaction = crate::transaction::test_helpers::sample_fee_transaction(rng);

        // Extract the rejected deployment.
        let rejected = crate::rejected::test_helpers::sample_rejected_deployment(rng);

        // Return the confirmed transaction.
        ConfirmedTransaction::rejected_deploy(index, fee_transaction, rejected).unwrap()
    }

    /// Samples a rejected execute transaction at the given index.
    pub(crate) fn sample_rejected_execute(index: u32, rng: &mut TestRng) -> ConfirmedTransaction<CurrentNetwork> {
        // Sample a fee transaction.
        let fee_transaction = crate::transaction::test_helpers::sample_fee_transaction(rng);

        // Extract the rejected execution.
        let rejected = crate::rejected::test_helpers::sample_rejected_execution(rng);

        // Return the confirmed transaction.
        ConfirmedTransaction::rejected_execute(index, fee_transaction, rejected).unwrap()
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

#[cfg(test)]
mod test {

    use super::*;

    #[test]
    fn test_accepted_execute() {
        let rng = &mut TestRng::default();

        let index = Uniform::rand(rng);
        let tx = crate::transaction::test_helpers::sample_execution_transaction_with_fee(rng);

        // Create an `AcceptedExecution` with valid `FinalizeOperation`s.
        let finalize_operations = vec![
            FinalizeOperation::InsertKeyValue(Uniform::rand(rng), Uniform::rand(rng), Uniform::rand(rng)),
            FinalizeOperation::UpdateKeyValue(
                Uniform::rand(rng),
                Uniform::rand(rng),
                Uniform::rand(rng),
                Uniform::rand(rng),
            ),
            FinalizeOperation::RemoveKeyValue(Uniform::rand(rng), Uniform::rand(rng)),
        ];
        let confirmed = ConfirmedTransaction::accepted_execute(index, tx.clone(), finalize_operations.clone()).unwrap();

        assert_eq!(confirmed.index(), index);
        assert_eq!(confirmed.transaction(), &tx);
        assert_eq!(confirmed.num_finalize(), finalize_operations.len());
        assert_eq!(confirmed.finalize_operations().unwrap(), &finalize_operations);

        // Attempt to create an `AcceptedExecution` with invalid `FinalizeOperation`s.
        let finalize_operations = vec![FinalizeOperation::InitializeMapping(Uniform::rand(rng))];
        let confirmed = ConfirmedTransaction::accepted_execute(index, tx.clone(), finalize_operations);
        assert!(confirmed.is_err());

        let finalize_operations = vec![FinalizeOperation::RemoveMapping(Uniform::rand(rng))];
        let confirmed = ConfirmedTransaction::accepted_execute(index, tx, finalize_operations);
        assert!(confirmed.is_err());
    }
}
