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

impl<E: Environment, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> Pedersen<E, NUM_WINDOWS, WINDOW_SIZE> {
    /// Returns the Pedersen hash of the given input as a field element.
    pub fn hash(&self, input: &[Boolean<E>]) -> Field<E> {
        // Compute the Pedersen hash as an affine group element, and return the x-coordinate.
        self.hash_uncompressed(input).to_x_coordinate()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_algorithms::{crh::PedersenCompressedCRH, CRH};
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_curves::AffineCurve;
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: usize = 10;
    const MESSAGE: &str = "PedersenCircuit0";
    const WINDOW_SIZE_MULTIPLIER: usize = 8;

    type Projective = <<Circuit as Environment>::Affine as AffineCurve>::Projective;

    fn check_hash<const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>(mode: Mode) {
        // Initialize the Pedersen hash.
        let native = PedersenCompressedCRH::<Projective, NUM_WINDOWS, WINDOW_SIZE>::setup(MESSAGE);
        let circuit = Pedersen::<Circuit, NUM_WINDOWS, WINDOW_SIZE>::setup(MESSAGE);
        // Determine the number of inputs.
        let num_input_bits = NUM_WINDOWS * WINDOW_SIZE;

        for i in 0..ITERATIONS {
            // Sample a random input.
            let input = (0..num_input_bits).map(|_| bool::rand(&mut test_rng())).collect::<Vec<bool>>();
            // Compute the expected hash.
            let expected = native.hash(&input).expect("Failed to hash native input");
            // Prepare the circuit input.
            let circuit_input: Vec<Boolean<_>> = Inject::new(mode, input);

            Circuit::scope(format!("Pedersen {mode} {i}"), || {
                // Perform the hash operation.
                let candidate = circuit.hash(&circuit_input);
                assert_eq!(expected, candidate.eject_value());
            });
        }
    }

    #[test]
    fn test_hash_constant() {
        check_hash::<1, WINDOW_SIZE_MULTIPLIER>(Mode::Constant);
        check_hash::<2, { 2 * WINDOW_SIZE_MULTIPLIER }>(Mode::Constant);
        check_hash::<3, { 3 * WINDOW_SIZE_MULTIPLIER }>(Mode::Constant);
        check_hash::<4, { 4 * WINDOW_SIZE_MULTIPLIER }>(Mode::Constant);
        check_hash::<5, { 5 * WINDOW_SIZE_MULTIPLIER }>(Mode::Constant);
    }

    #[test]
    fn test_hash_public() {
        check_hash::<1, WINDOW_SIZE_MULTIPLIER>(Mode::Public);
        check_hash::<2, { 2 * WINDOW_SIZE_MULTIPLIER }>(Mode::Public);
        check_hash::<3, { 3 * WINDOW_SIZE_MULTIPLIER }>(Mode::Public);
        check_hash::<4, { 4 * WINDOW_SIZE_MULTIPLIER }>(Mode::Public);
        check_hash::<5, { 5 * WINDOW_SIZE_MULTIPLIER }>(Mode::Public);
    }

    #[test]
    fn test_hash_private() {
        check_hash::<1, WINDOW_SIZE_MULTIPLIER>(Mode::Private);
        check_hash::<2, { 2 * WINDOW_SIZE_MULTIPLIER }>(Mode::Private);
        check_hash::<3, { 3 * WINDOW_SIZE_MULTIPLIER }>(Mode::Private);
        check_hash::<4, { 4 * WINDOW_SIZE_MULTIPLIER }>(Mode::Private);
        check_hash::<5, { 5 * WINDOW_SIZE_MULTIPLIER }>(Mode::Private);
    }
}
