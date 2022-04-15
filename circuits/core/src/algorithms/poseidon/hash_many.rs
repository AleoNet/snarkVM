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

impl<E: Environment> HashMany for Poseidon<E> {
    type Input = Field<E>;
    type Output = Field<E>;

    #[inline]
    fn hash_many(&self, input: &[Self::Input], num_outputs: usize) -> Vec<Self::Output> {
        // Initialize a new sponge.
        let mut state = vec![Field::zero(); RATE + CAPACITY];
        let mut mode = DuplexSpongeMode::Absorbing { next_absorb_index: 0 };

        // Absorb the input and squeeze the output.
        self.absorb(&mut state, &mut mode, input);
        self.squeeze(&mut state, &mut mode, num_outputs)
    }
}

impl<E: Environment> Count<dyn HashMany<Input = Field<E>, Output = Field<E>>> for Poseidon<E> {
    type Case = ();

    fn count(_parameter: &Self::Case) -> CircuitCount {
        todo!()
    }
}

impl<E: Environment> OutputMode<dyn HashMany<Input = Field<E>, Output = Field<E>>> for Poseidon<E> {
    type Case = ();

    fn output_mode(_parameter: &Self::Case) -> Mode {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_algorithms::crypto_hash::Poseidon as NativePoseidon;
    use snarkvm_circuits_types::environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: usize = 10;

    fn check_hash_many(
        mode: Mode,
        num_inputs: usize,
        num_outputs: usize,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        let rng = &mut test_rng();
        let native_poseidon = NativePoseidon::<_, RATE, OPTIMIZED_FOR_WEIGHTS>::setup();
        let poseidon = Poseidon::new();

        for i in 0..ITERATIONS {
            // Prepare the preimage.
            let native_input =
                (0..num_inputs).map(|_| <Circuit as Environment>::BaseField::rand(rng)).collect::<Vec<_>>();
            let input = native_input.iter().map(|v| Field::<Circuit>::new(mode, *v)).collect::<Vec<_>>();

            // Compute the native hash.
            let expected = native_poseidon.evaluate_many(&native_input, num_outputs);
            // Compute the circuit hash.
            Circuit::scope(format!("Poseidon {mode} {i} {num_outputs}"), || {
                let candidate = poseidon.hash_many(&input, num_outputs);
                for (expected_element, candidate_element) in expected.iter().zip_eq(&candidate) {
                    assert_eq!(*expected_element, candidate_element.eject_value());
                }
                let case = format!("(mode = {mode}, num_inputs = {num_inputs}, num_outputs = {num_outputs})");
                assert_scope!(case, num_constants, num_public, num_private, num_constraints);
            });
        }
    }

    #[test]
    fn test_hash_many_constant() {
        for num_inputs in 0..=RATE {
            for num_outputs in 0..=RATE {
                check_hash_many(Mode::Constant, num_inputs, num_outputs, 0, 0, 0, 0);
            }
        }
    }

    #[test]
    fn test_hash_many_public() {
        for num_outputs in 0..=RATE {
            check_hash_many(Mode::Public, 0, num_outputs, 0, 0, 0, 0);
        }
        for num_outputs in 1..=RATE {
            check_hash_many(Mode::Public, 1, num_outputs, 0, 0, 335, 335);
            check_hash_many(Mode::Public, 2, num_outputs, 0, 0, 340, 340);
            check_hash_many(Mode::Public, 3, num_outputs, 0, 0, 345, 345);
            check_hash_many(Mode::Public, 4, num_outputs, 0, 0, 350, 350);
            check_hash_many(Mode::Public, 5, num_outputs, 0, 0, 705, 705);
            check_hash_many(Mode::Public, 6, num_outputs, 0, 0, 705, 705);
        }
        for num_outputs in (RATE + 1)..=(RATE * 2) {
            check_hash_many(Mode::Public, 1, num_outputs, 0, 0, 690, 690);
            check_hash_many(Mode::Public, 2, num_outputs, 0, 0, 695, 695);
            check_hash_many(Mode::Public, 3, num_outputs, 0, 0, 700, 700);
            check_hash_many(Mode::Public, 4, num_outputs, 0, 0, 705, 705);
            check_hash_many(Mode::Public, 5, num_outputs, 0, 0, 1060, 1060);
            check_hash_many(Mode::Public, 6, num_outputs, 0, 0, 1060, 1060);
        }
    }

    #[test]
    fn test_hash_many_private() {
        for num_outputs in 0..=RATE {
            check_hash_many(Mode::Private, 0, num_outputs, 0, 0, 0, 0);
        }
        for num_outputs in 1..=RATE {
            check_hash_many(Mode::Private, 1, num_outputs, 0, 0, 335, 335);
            check_hash_many(Mode::Private, 2, num_outputs, 0, 0, 340, 340);
            check_hash_many(Mode::Private, 3, num_outputs, 0, 0, 345, 345);
            check_hash_many(Mode::Private, 4, num_outputs, 0, 0, 350, 350);
            check_hash_many(Mode::Private, 5, num_outputs, 0, 0, 705, 705);
            check_hash_many(Mode::Private, 6, num_outputs, 0, 0, 705, 705);
        }
        for num_outputs in (RATE + 1)..=(RATE * 2) {
            check_hash_many(Mode::Private, 1, num_outputs, 0, 0, 690, 690);
            check_hash_many(Mode::Private, 2, num_outputs, 0, 0, 695, 695);
            check_hash_many(Mode::Private, 3, num_outputs, 0, 0, 700, 700);
            check_hash_many(Mode::Private, 4, num_outputs, 0, 0, 705, 705);
            check_hash_many(Mode::Private, 5, num_outputs, 0, 0, 1060, 1060);
            check_hash_many(Mode::Private, 6, num_outputs, 0, 0, 1060, 1060);
        }
    }
}
