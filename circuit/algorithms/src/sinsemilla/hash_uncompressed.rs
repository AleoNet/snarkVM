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

use std::borrow::Cow;

impl<E: Lookup + Environment, const NUM_WINDOWS: u8> HashUncompressed for Sinsemilla<E, NUM_WINDOWS> {
    type Input = Boolean<E>;
    type Output = Group<E>;

    fn hash_uncompressed(&self, input: &[Self::Input]) -> Self::Output {
        // Ensure the input size is within the size bounds.
        let mut input = Cow::Borrowed(input);
        let max_len = console::SINSEMILLA_WINDOW_SIZE * NUM_WINDOWS as usize;
        match input.len() <= max_len {
            // Pad the input if it is under the required parameter size.
            true => input.to_mut().resize(max_len, Boolean::constant(false)),
            // Ensure the input size is within the parameter size.
            false => E::halt(format!("The Sinsemilla hash input cannot exceed {} bits.", max_len)),
        }

        input.chunks(console::SINSEMILLA_WINDOW_SIZE).fold(self.q.clone(), |acc, bits| {
            let i = Field::from_bits_le(bits);
            match E::unary_lookup(0, i) {
                Ok((s_x, s_y)) => {
                    let s = Group::from_xy_coordinates(
                        Field::from(LinearCombination::from(s_x)),
                        Field::from(LinearCombination::from(s_y)),
                    );
                    acc.double() + s
                }
                Err(e) => E::halt(e.to_string()),
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_types::environment::Circuit;
    use snarkvm_utilities::{TestRng, Uniform};

    const ITERATIONS: u64 = 10;
    const MESSAGE: &str = "SinsemillaCircuit0";

    fn check_hash_uncompressed<const NUM_WINDOWS: u8>(mode: Mode) {
        use console::Hash as H;

        let mut rng = TestRng::default();

        // Initialize the Sinsemilla hash.
        let native = console::Sinsemilla::<<Circuit as Environment>::Network, NUM_WINDOWS>::setup(MESSAGE);
        let circuit = Sinsemilla::<Circuit, NUM_WINDOWS>::new(Mode::Constant, native);

        let native = console::Sinsemilla::<<Circuit as Environment>::Network, NUM_WINDOWS>::setup(MESSAGE);
        // Determine the number of inputs.
        let num_input_bits = NUM_WINDOWS as usize * console::SINSEMILLA_WINDOW_SIZE;

        for i in 0..ITERATIONS {
            // Sample a random input.
            let input = (0..num_input_bits).map(|_| bool::rand(&mut rng)).collect::<Vec<bool>>();
            // Compute the expected hash.
            let expected = native.hash(&input).expect("Failed to hash native input");
            // Prepare the circuit input.
            let circuit_input: Vec<Boolean<_>> = Inject::new(mode, input);

            Circuit::scope(format!("Sinsemilla {mode} {i}"), || {
                // Perform the hash operation.
                let candidate = circuit.hash_uncompressed(&circuit_input);
                println!("{}", Circuit::num_constraints_in_scope());
                println!("{}", Circuit::num_constants_in_scope());
                assert_eq!(expected, candidate.eject_value().to_x_coordinate());
            });
        }
    }

    #[test]
    fn test_hash_uncompressed_constant() {
        // Set the number of windows, and modulate the window size.
        check_hash_uncompressed::<74>(Mode::Constant);
    }

    #[test]
    fn test_hash_uncompressed_public() {
        // Set the number of windows, and modulate the window size.
        check_hash_uncompressed::<74>(Mode::Public);
    }

    #[test]
    fn test_hash_uncompressed_private() {
        // Set the number of windows, and modulate the window size.
        check_hash_uncompressed::<74>(Mode::Private);
    }
}
