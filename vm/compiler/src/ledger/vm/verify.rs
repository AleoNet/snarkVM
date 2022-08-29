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

impl<N: Network, P: ProgramStorage<N>> VM<N, P> {
    /// Verifies the transaction in the VM.
    #[inline]
    pub fn verify(&self, transaction: &Transaction<N>) -> bool {
        // Compute the Merkle root of the transaction.
        match transaction.to_root() {
            // Ensure the transaction ID is correct.
            Ok(root) => {
                if *transaction.id() != root {
                    warn!("Incorrect transaction ID ({})", transaction.id());
                    return false;
                }
            }
            Err(error) => {
                warn!("Failed to compute the Merkle root of the transaction: {error}\n{transaction}");
                return false;
            }
        };

        // Ensure there are no duplicate transition IDs.
        if has_duplicates(transaction.transition_ids()) {
            warn!("Found duplicate transition in the transactions list");
            return false;
        }

        // Ensure there are no duplicate transition public keys.
        if has_duplicates(transaction.transition_public_keys()) {
            warn!("Found duplicate transition public keys in the transactions list");
            return false;
        }

        // Ensure there are no duplicate serial numbers.
        if has_duplicates(transaction.serial_numbers()) {
            warn!("Found duplicate serial numbers in the transactions list");
            return false;
        }

        // Ensure there are no duplicate commitments.
        if has_duplicates(transaction.commitments()) {
            warn!("Found duplicate commitments in the transactions list");
            return false;
        }

        // Ensure there are no duplicate nonces.
        if has_duplicates(transaction.nonces()) {
            warn!("Found duplicate nonces in the transactions list");
            return false;
        }

        match transaction {
            Transaction::Deploy(_, deployment, additional_fee) => {
                // Check the deployment size.
                if let Err(error) = Transaction::check_deployment_size(deployment) {
                    warn!("Invalid transaction size (deployment): {error}");
                    return false;
                }
                // Verify the deployment.
                self.verify_deployment(deployment)
                    // Verify the additional fee.
                    && self.verify_additional_fee(additional_fee)
            }
            Transaction::Execute(_, execution, additional_fee) => {
                // Check the deployment size.
                if let Err(error) = Transaction::check_execution_size(execution) {
                    warn!("Invalid transaction size (execution): {error}");
                    return false;
                }

                // Verify the additional fee, if it exists.
                let check_additional_fee = match additional_fee {
                    Some(additional_fee) => self.verify_additional_fee(additional_fee),
                    None => true,
                };

                // Verify the execution.
                self.verify_execution(execution)
                    // Verify the additional fee.
                    && check_additional_fee
            }
        }
    }

    /// Verifies the given deployment.
    #[inline]
    fn verify_deployment(&self, deployment: &Deployment<N>) -> bool {
        // Compute the core logic.
        macro_rules! logic {
            ($process:expr, $network:path, $aleo:path) => {{
                let task = || {
                    // Prepare the deployment.
                    let deployment = cast_ref!(&deployment as Deployment<$network>);
                    // Initialize an RNG.
                    let rng = &mut rand::thread_rng();
                    // Verify the deployment.
                    $process.verify_deployment::<$aleo, _>(&deployment, rng)
                };
                task()
            }};
        }

        // Process the logic.
        match process!(self, logic) {
            Ok(()) => true,
            Err(error) => {
                warn!("Deployment verification failed: {error}");
                false
            }
        }
    }

    /// Verifies the given execution.
    #[inline]
    fn verify_execution(&self, execution: &Execution<N>) -> bool {
        // Compute the core logic.
        macro_rules! logic {
            ($process:expr, $network:path, $aleo:path) => {{
                let task = || {
                    // Prepare the execution.
                    let execution = cast_ref!(&execution as Execution<$network>);
                    // Verify the execution.
                    $process.verify_execution(execution)
                };
                task()
            }};
        }

        // Process the logic.
        match process!(self, logic) {
            Ok(()) => true,
            Err(error) => {
                warn!("Execution verification failed: {error}");
                false
            }
        }
    }

    /// Verifies the given additional fee.
    #[inline]
    fn verify_additional_fee(&self, additional_fee: &AdditionalFee<N>) -> bool {
        // Compute the core logic.
        macro_rules! logic {
            ($process:expr, $network:path, $aleo:path) => {{
                let task = || {
                    // Prepare the additional fee.
                    let additional_fee = cast_ref!(&additional_fee as AdditionalFee<$network>);
                    // Verify the additional fee.
                    $process.verify_additional_fee(additional_fee)
                };
                task()
            }};
        }

        // Process the logic.
        match process!(self, logic) {
            Ok(()) => true,
            Err(error) => {
                warn!("Additional fee verification failed: {error}");
                false
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::ledger::vm::test_helpers::sample_program;
    use snarkvm_utilities::TestRng;

    #[test]
    fn test_verify() {
        let rng = &mut TestRng::default();
        let vm = crate::ledger::vm::test_helpers::sample_vm();

        // Fetch a deployment transaction.
        let deployment_transaction = crate::ledger::vm::test_helpers::sample_deployment_transaction(rng);
        // Ensure the transaction verifies.
        assert!(vm.verify(&deployment_transaction));

        // Fetch a execution transaction.
        let execution_transaction = crate::ledger::vm::test_helpers::sample_execution_transaction(rng);
        // Ensure the transaction verifies.
        assert!(vm.verify(&execution_transaction));
    }

    #[test]
    fn test_verify_deployment() {
        let rng = &mut TestRng::default();
        let vm = crate::ledger::vm::test_helpers::sample_vm();

        // Fetch the program from the deployment.
        let program = sample_program();

        // Deploy the program.
        let deployment = vm.deploy(&program, rng).unwrap();

        // Ensure the deployment is valid.
        assert!(vm.verify_deployment(&deployment));
    }
}
