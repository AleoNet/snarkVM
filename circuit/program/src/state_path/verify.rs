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

impl<A: Aleo> StatePath<A> {
    /// Returns `true` if the state path is valid.
    ///
    /// # Parameters
    ///  - `local_state_root` is the local transaction root for the current execution.
    ///  - `is_global` is a boolean indicating whether this is a global or local state root.
    ///
    /// # Diagram
    /// The `[[ ]]` notation is used to denote public inputs.
    /// ```ignore
    ///
    ///  [[ global_state_root ]]
    ///           |
    ///      block_path
    ///          |
    ///     block_hash := Hash( previous_block_hash || header_root )
    ///                                                     |
    ///                                                header_path
    ///                                                    |
    ///                                               header_leaf
    ///                                                   |
    ///                                            transactions_path          [[ local_state_root ]]
    ///                                                  |                               |
    ///                                               (true) ------ is_global ------ (false)
    ///                                                                 |
    ///                                                          transaction_id
    ///                                                                |
    ///                                                        transaction_path
    ///                                                               |
    ///                                                       transaction_leaf
    ///                                                              |
    ///                                                      transition_path
    ///                                                             |
    ///                                                    transition_leaf
    /// ```
    pub fn verify(&self, is_global: &Boolean<A>, local_state_root: &Field<A>) -> Boolean<A> {
        // Ensure the transition path is valid.
        let check_transition_path = A::verify_merkle_path_bhp(
            &self.transition_path,
            self.transaction_leaf.id(),
            &self.transition_leaf.to_bits_le(),
        ) & self.transition_leaf.variant().is_equal(&U16::constant(console::U16::new(3))); // Variant = 3 (Input::Record)

        // Ensure the transaction path is valid.
        let check_transaction_path = A::verify_merkle_path_bhp(
            &self.transaction_path,
            &self.transaction_id,
            &self.transaction_leaf.to_bits_le(),
        ) & self.transaction_leaf.variant().is_equal(&U8::one()); // Variant = 1 (Transaction::Execution)

        // Ensure the transactions path is valid.
        let check_transactions_path = A::verify_merkle_path_bhp(
            &self.transactions_path,
            self.header_leaf.id(),
            &self.transaction_id.to_bits_le(),
        );

        // Ensure the header path is valid.
        let check_header_path =
            A::verify_merkle_path_bhp(&self.header_path, &self.header_root, &self.header_leaf.to_bits_le())
                & self.header_leaf.index().is_equal(&U8::one()); // Index = 1 (Header::transactions_root)

        // Construct the block hash preimage.
        let block_hash_preimage = self
            .previous_block_hash
            .to_bits_le()
            .into_iter()
            .chain(self.header_root.to_bits_le().into_iter())
            .collect::<Vec<_>>();

        // Ensure the block path is valid.
        let check_block_hash = A::hash_bhp1024(&block_hash_preimage).is_equal(&self.block_hash);

        // Ensure the global state root is correct.
        let check_state_root =
            A::verify_merkle_path_bhp(&self.block_path, &self.global_state_root, &self.block_hash.to_bits_le());

        // Combine the transition and transaction path checks.
        let check_transition_and_transaction_path = check_transition_path & check_transaction_path;

        // Check the state path.
        let check_local = &check_transition_and_transaction_path & local_state_root.is_equal(&self.transaction_id);
        let check_global = check_transition_and_transaction_path
            & check_transactions_path
            & check_header_path
            & check_block_hash
            & check_state_root;

        // If the state path is for a global root, return 'check_global'. Else, return 'check_local'.
        Boolean::ternary(is_global, &check_global, &check_local)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::rand::{TestRng, Uniform};

    type CurrentAleo = Circuit;
    type CurrentNetwork = <Circuit as Environment>::Network;

    const ITERATIONS: usize = 20;

    #[test]
    fn test_verify_global() {
        let rng = &mut TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample the console state path.
            let console_state_path =
                console::state_path::test_helpers::sample_global_state_path::<CurrentNetwork>(None, rng).unwrap();
            // Sample the local state root.
            let local_state_root = console::Field::rand(rng);

            // Ensure the console state path is valid.
            console_state_path.verify(true, local_state_root).unwrap();

            for mode in [Mode::Constant, Mode::Public, Mode::Private].into_iter() {
                // Inject the is_global boolean.
                let circuit_is_global = Boolean::new(mode, true);
                // Inject the local state root.
                let circuit_local_state_root = Field::new(mode, local_state_root);
                // Inject the state path.
                let circuit_state_path = StatePath::<CurrentAleo>::new(mode, console_state_path.clone());

                // Ensure the state path is valid.
                let is_valid = circuit_state_path.verify(&circuit_is_global, &circuit_local_state_root);
                assert!(is_valid.eject_value());
                assert!(CurrentAleo::is_satisfied());
                CurrentAleo::reset();

                // Inject the is_global boolean.
                let circuit_is_global = Boolean::new(mode, false);

                // Ensure the state path is *not* valid for a random local state root.
                let is_valid = circuit_state_path.verify(&circuit_is_global, &circuit_local_state_root);
                assert!(!is_valid.eject_value());
                assert!(CurrentAleo::is_satisfied());
                CurrentAleo::reset();
            }
        }
    }

    #[test]
    fn test_verify_local() {
        let rng = &mut TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample the console state path.
            let console_state_path =
                console::state_path::test_helpers::sample_local_state_path::<CurrentNetwork>(None, rng).unwrap();
            // Sample the local state root.
            let local_state_root = **console_state_path.transaction_id();

            // Ensure the console state path is valid.
            console_state_path.verify(false, local_state_root).unwrap();

            for mode in [Mode::Constant, Mode::Public, Mode::Private].into_iter() {
                // Inject the is_global boolean.
                let circuit_is_global = Boolean::new(mode, false);
                // Inject the local state root.
                let circuit_local_state_root = Field::new(mode, local_state_root);
                // Inject the state path.
                let circuit_state_path = StatePath::<CurrentAleo>::new(mode, console_state_path.clone());

                // Ensure the state path is valid.
                let is_valid = circuit_state_path.verify(&circuit_is_global, &circuit_local_state_root);
                assert!(is_valid.eject_value());
                assert!(CurrentAleo::is_satisfied());
                CurrentAleo::reset();

                // Inject the is_global boolean.
                let circuit_is_global = Boolean::new(mode, false);
                // Inject a random local state root.
                let circuit_local_state_root = Field::new(mode, console::Field::rand(rng));

                // Ensure the state path does *not* match a random local state root.
                let is_valid = circuit_state_path.verify(&circuit_is_global, &circuit_local_state_root);
                assert!(!is_valid.eject_value());
                assert!(CurrentAleo::is_satisfied());
                CurrentAleo::reset();

                // Inject the is_global boolean.
                let circuit_is_global = Boolean::new(mode, true);
                // Inject a random local state root.
                let circuit_local_state_root = Field::new(mode, local_state_root);

                // Ensure the state path does *not* match to the random global state root.
                let is_valid = circuit_state_path.verify(&circuit_is_global, &circuit_local_state_root);
                assert!(!is_valid.eject_value());
                assert!(CurrentAleo::is_satisfied());
                CurrentAleo::reset();
            }
        }
    }
}
