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

// TODO (raychu86): Inject this check into the `execute` call.

impl<A: Aleo> StatePath<A> {
    /// Returns `true` if the state path is valid.
    pub fn verify(&self) -> Boolean<A> {
        // Ensure the transition path is valid.
        let check_transition_path = A::verify_merkle_path_bhp(
            &self.transition_path,
            self.transaction_leaf.id(),
            &self.transition_leaf.to_bits_le(),
        );

        // Ensure the transaction path is valid.
        let check_transaction_path = A::verify_merkle_path_bhp(
            &self.transaction_path,
            &self.transaction_id,
            &self.transaction_leaf.to_bits_le(),
        );

        // Ensure the transactions path is valid.
        let check_transactions_path = A::verify_merkle_path_bhp(
            &self.transactions_path,
            self.header_leaf.id(),
            &self.transaction_id.to_bits_le(),
        );

        // Ensure the header path is valid.
        let check_header_path =
            A::verify_merkle_path_bhp(&self.header_path, &self.header_root, &self.header_leaf.to_bits_le());

        // Construct the block hash preimage.
        let block_hash_preimage = self
            .previous_block_hash
            .to_bits_le()
            .into_iter()
            .chain(self.header_root.to_bits_le().into_iter())
            .collect::<Vec<_>>();

        // Ensure the block path is valid.
        let check_block_hash = A::hash_bhp1024(&block_hash_preimage).is_equal(&self.block_hash);

        // Ensure the state root is correct.
        let check_state_root =
            A::verify_merkle_path_bhp(&self.block_path, &self.state_root, &self.block_hash.to_bits_le());

        check_transition_path
            .is_equal(&check_transaction_path)
            .is_equal(&check_transactions_path)
            .is_equal(&check_header_path)
            .is_equal(&check_block_hash)
            .is_equal(&check_state_root)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        ledger::{state_path::circuit::StatePath as StatePathCircuit, test_helpers::CurrentLedger},
        UniversalSRS,
    };
    use circuit::{
        environment::{Circuit, Inject},
        network::AleoV0,
        Mode,
    };
    use console::{network::Testnet3, program::Identifier};
    use snarkvm_utilities::rand::TestRng;

    type CurrentAleo = AleoV0;
    type CurrentNetwork = Testnet3;

    fn construct_state_path_circuit(ledger: &CurrentLedger, mode: Mode) {
        // Retrieve the genesis block.
        let genesis = ledger.get_block(0).unwrap();

        // Construct the native state path.
        let commitments = genesis.transactions().commitments().collect::<Vec<_>>();
        let commitment = commitments[0];
        let native_state_path = ledger.to_state_path(commitment).unwrap();

        // Construct the circuit state path
        let circuit_state_path = StatePathCircuit::<CurrentAleo>::new(mode, native_state_path);

        let is_valid = circuit_state_path.verify();
        assert!(is_valid.eject_value());
        assert!(CurrentAleo::is_satisfied());
    }

    #[test]
    fn test_state_path_verify() {
        // Initialize a new ledger.
        let ledger = CurrentLedger::new(None).unwrap();

        construct_state_path_circuit(&ledger, Mode::Public);
    }

    fn test_state_path_verify_num_constraints(mode: Mode, batch_size: usize) {
        let rng = &mut TestRng::default();

        // Initialize a new ledger.
        let ledger = CurrentLedger::new(None).unwrap();

        // Construct the assignments.
        let mut assignments = Vec::with_capacity(batch_size);
        for _ in 0..batch_size {
            construct_state_path_circuit(&ledger, mode);
            let assignment = CurrentAleo::eject_assignment_and_reset();
            Circuit::reset();

            assignments.push(assignment);
        }

        // Construct the proving and verifying keys.
        let universal_srs = UniversalSRS::<CurrentNetwork>::load().unwrap();
        let function_name =
            Identifier::<CurrentNetwork>::try_from(format!("state_paths_{batch_size}").as_str()).unwrap();
        let (proving_key, verifying_key) = universal_srs.to_circuit_key(&function_name, &assignments[0]).unwrap();

        // Generate the batch proof.
        let batch_proof = proving_key.prove_batch(&function_name, &assignments, rng).unwrap();

        // Verify the batch proof.
        let one = <Circuit as Environment>::BaseField::one();
        let batch_verify =
            verifying_key.verify_batch(&function_name, vec![vec![one].as_slice(); batch_size].as_slice(), &batch_proof);

        assert!(batch_verify);
    }

    #[test]
    fn test_state_path_batch_1() {
        test_state_path_verify_num_constraints(Mode::Private, 1);
    }

    #[test]
    fn test_state_path_batch_2() {
        test_state_path_verify_num_constraints(Mode::Private, 2);
    }

    #[test]
    fn test_state_path_batch_4() {
        test_state_path_verify_num_constraints(Mode::Private, 4);
    }

    #[test]
    fn test_state_path_batch_8() {
        test_state_path_verify_num_constraints(Mode::Private, 8);
    }
}
