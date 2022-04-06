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

use snarkvm_circuits_types::prelude::*;

impl<E: Environment, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> Pedersen<E, NUM_WINDOWS, WINDOW_SIZE> {
    /// Returns the Pedersen commitment of the given input with the given randomness
    /// as an affine group element.
    pub fn commit(&self, input: &[Boolean<E>], randomness: &[Boolean<E>]) -> Group<E> {
        let hash = self.hash_uncompressed(input);

        // Compute h^r
        randomness
            .iter()
            .zip_eq(&self.random_base)
            .map(|(bit, power)| Group::ternary(bit, power, &Group::zero()))
            .fold(hash, |acc, x| acc + x)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_algorithms::{commitment::PedersenCommitment as NativePedersenCommitment, CommitmentScheme};
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_curves::AffineCurve;
    use snarkvm_utilities::{test_rng, ToBits, UniformRand};

    const ITERATIONS: usize = 10;
    const MESSAGE: &str = "PedersenCommitmentCircuit0";
    const WINDOW_SIZE_MULTIPLIER: usize = 8;

    type Projective = <<Circuit as Environment>::Affine as AffineCurve>::Projective;
    type ScalarField = <Circuit as Environment>::ScalarField;

    fn check_commitment<const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>(
        mode: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        // Initialize the Pedersen hash.
        let native = NativePedersenCommitment::<Projective, NUM_WINDOWS, WINDOW_SIZE>::setup(MESSAGE);
        let circuit = Pedersen::<Circuit, NUM_WINDOWS, WINDOW_SIZE>::setup(MESSAGE);
        // Determine the number of inputs.
        let num_input_bits = NUM_WINDOWS * WINDOW_SIZE;

        for i in 0..ITERATIONS {
            // Sample a random input.
            let input = (0..num_input_bits).map(|_| bool::rand(&mut test_rng())).collect::<Vec<bool>>();
            // Sample randomness
            let randomness = ScalarField::rand(&mut test_rng());
            // Compute the expected hash.
            let expected = native.commit(&input, &randomness).expect("Failed to hash native input");
            // Prepare the circuit input.
            let circuit_input: Vec<Boolean<_>> = Inject::new(mode, input);
            // Prepare the circuit randomness.
            let circuit_randomness: Vec<Boolean<_>> = Inject::new(mode, randomness.to_bits_le());

            Circuit::scope(format!("Pedersen {mode} {i}"), || {
                // Perform the hash operation.
                let candidate = circuit.commit(&circuit_input, &circuit_randomness);
                assert_scope!(num_constants, num_public, num_private, num_constraints);
                assert_eq!(expected, candidate.eject_value());
            });
        }
    }

    #[test]
    fn test_commitment_constant() {
        // Set the number of windows, and modulate the window size.
        check_commitment::<1, WINDOW_SIZE_MULTIPLIER>(Mode::Constant, 1036, 0, 0, 0);
        check_commitment::<1, { 2 * WINDOW_SIZE_MULTIPLIER }>(Mode::Constant, 1068, 0, 0, 0);
        check_commitment::<1, { 3 * WINDOW_SIZE_MULTIPLIER }>(Mode::Constant, 1100, 0, 0, 0);
        check_commitment::<1, { 4 * WINDOW_SIZE_MULTIPLIER }>(Mode::Constant, 1132, 0, 0, 0);
        check_commitment::<1, { 5 * WINDOW_SIZE_MULTIPLIER }>(Mode::Constant, 1164, 0, 0, 0);

        // Set the window size, and modulate the number of windows.
        check_commitment::<1, WINDOW_SIZE_MULTIPLIER>(Mode::Constant, 1036, 0, 0, 0);
        check_commitment::<2, WINDOW_SIZE_MULTIPLIER>(Mode::Constant, 1068, 0, 0, 0);
        check_commitment::<3, WINDOW_SIZE_MULTIPLIER>(Mode::Constant, 1100, 0, 0, 0);
        check_commitment::<4, WINDOW_SIZE_MULTIPLIER>(Mode::Constant, 1132, 0, 0, 0);
        check_commitment::<5, WINDOW_SIZE_MULTIPLIER>(Mode::Constant, 1164, 0, 0, 0);
    }

    #[test]
    fn test_commitment_public() {
        // Set the number of windows, and modulate the window size.
        check_commitment::<1, WINDOW_SIZE_MULTIPLIER>(Mode::Public, 518, 0, 1551, 1551);
        check_commitment::<1, { 2 * WINDOW_SIZE_MULTIPLIER }>(Mode::Public, 534, 0, 1599, 1599);
        check_commitment::<1, { 3 * WINDOW_SIZE_MULTIPLIER }>(Mode::Public, 550, 0, 1647, 1647);
        check_commitment::<1, { 4 * WINDOW_SIZE_MULTIPLIER }>(Mode::Public, 566, 0, 1695, 1695);
        check_commitment::<1, { 5 * WINDOW_SIZE_MULTIPLIER }>(Mode::Public, 582, 0, 1743, 1743);

        // Set the window size, and modulate the number of windows.
        check_commitment::<1, WINDOW_SIZE_MULTIPLIER>(Mode::Public, 518, 0, 1551, 1551);
        check_commitment::<2, WINDOW_SIZE_MULTIPLIER>(Mode::Public, 534, 0, 1599, 1599);
        check_commitment::<3, WINDOW_SIZE_MULTIPLIER>(Mode::Public, 550, 0, 1647, 1647);
        check_commitment::<4, WINDOW_SIZE_MULTIPLIER>(Mode::Public, 566, 0, 1695, 1695);
        check_commitment::<5, WINDOW_SIZE_MULTIPLIER>(Mode::Public, 582, 0, 1743, 1743);
    }

    #[test]
    fn test_commitment_private() {
        // Set the number of windows, and modulate the window size.
        check_commitment::<1, WINDOW_SIZE_MULTIPLIER>(Mode::Private, 518, 0, 1551, 1551);
        check_commitment::<1, { 2 * WINDOW_SIZE_MULTIPLIER }>(Mode::Private, 534, 0, 1599, 1599);
        check_commitment::<1, { 3 * WINDOW_SIZE_MULTIPLIER }>(Mode::Private, 550, 0, 1647, 1647);
        check_commitment::<1, { 4 * WINDOW_SIZE_MULTIPLIER }>(Mode::Private, 566, 0, 1695, 1695);
        check_commitment::<1, { 5 * WINDOW_SIZE_MULTIPLIER }>(Mode::Private, 582, 0, 1743, 1743);

        // Set the window size, and modulate the number of windows.
        check_commitment::<1, WINDOW_SIZE_MULTIPLIER>(Mode::Private, 518, 0, 1551, 1551);
        check_commitment::<2, WINDOW_SIZE_MULTIPLIER>(Mode::Private, 534, 0, 1599, 1599);
        check_commitment::<3, WINDOW_SIZE_MULTIPLIER>(Mode::Private, 550, 0, 1647, 1647);
        check_commitment::<4, WINDOW_SIZE_MULTIPLIER>(Mode::Private, 566, 0, 1695, 1695);
        check_commitment::<5, WINDOW_SIZE_MULTIPLIER>(Mode::Private, 582, 0, 1743, 1743);
    }
}
