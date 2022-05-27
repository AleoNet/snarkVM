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

impl<E: Environment, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> CommitUncompressed
    for BHP<E, NUM_WINDOWS, WINDOW_SIZE>
{
    type Input = Boolean<E>;
    type Output = Group<E>;
    type Randomizer = Scalar<E>;

    /// Returns the BHP commitment of the given input and randomizer as an affine group element.
    fn commit_uncompressed(&self, input: &[Self::Input], randomizer: &Self::Randomizer) -> Self::Output {
        let hash = self.hash_uncompressed(input);

        // Compute h^r.
        randomizer
            .to_bits_le()
            .iter()
            .zip_eq(&self.random_base)
            .map(|(bit, power)| Group::ternary(bit, power, &Group::zero()))
            .fold(hash, |acc, x| acc + x)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;
    use snarkvm_console_algorithms::{CommitUncompressed as C, BHP as NativeBHP};
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: usize = 10;
    const MESSAGE: &str = "BHPCircuit0";

    fn check_commit_uncompressed<const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>(
        mode: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) {
        // Initialize BHP.
        let native = NativeBHP::<<Circuit as Environment>::Affine, NUM_WINDOWS, WINDOW_SIZE>::setup(MESSAGE);
        let circuit = BHP::<Circuit, NUM_WINDOWS, WINDOW_SIZE>::setup(MESSAGE);
        // Determine the number of inputs.
        let num_input_bits = NUM_WINDOWS * WINDOW_SIZE * BHP_CHUNK_SIZE;

        for i in 0..ITERATIONS {
            // Sample a random input.
            let input = (0..num_input_bits).map(|_| bool::rand(&mut test_rng())).collect::<Vec<bool>>();
            // Sample a randomizer.
            let randomizer = UniformRand::rand(&mut test_rng());
            // Compute the expected commitment.
            let expected = native.commit_uncompressed(&input, &randomizer).expect("Failed to commit native input");
            // Prepare the circuit input.
            let circuit_input: Vec<Boolean<_>> = Inject::new(mode, input);
            // Prepare the circuit randomizer.
            let circuit_randomizer: Scalar<_> = Inject::new(mode, randomizer);

            Circuit::scope(format!("BHP {mode} {i}"), || {
                // Perform the hash operation.
                let candidate = circuit.commit_uncompressed(&circuit_input, &circuit_randomizer);
                assert_scope!(<=num_constants, num_public, num_private, num_constraints);
                assert_eq!(expected, candidate.eject_value());
            });
        }
    }

    #[test]
    fn test_commit_uncompressed_constant() {
        check_commit_uncompressed::<32, 48>(Mode::Constant, 6879, 0, 0, 0);
    }

    #[test]
    fn test_commit_uncompressed_public() {
        check_commit_uncompressed::<32, 48>(Mode::Public, 631, 0, 9404, 9404);
    }

    #[test]
    fn test_commit_uncompressed_private() {
        check_commit_uncompressed::<32, 48>(Mode::Private, 631, 0, 9404, 9404);
    }
}
