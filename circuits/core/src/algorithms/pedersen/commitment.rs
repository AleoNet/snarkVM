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

use snarkvm_algorithms::crypto_hash::hash_to_curve;
use snarkvm_circuits_types::prelude::*;

/// PedersenCommitment64 is an *additively-homomorphic* commitment scheme that takes a 64-bit input.
pub type PedersenCommitment64<E> = PedersenCommitment<E, 1, 64>;
/// PedersenCommitment128 is an *additively-homomorphic* commitment scheme that takes a 128-bit input.
pub type PedersenCommitment128<E> = PedersenCommitment<E, 1, 128>;
/// PedersenCommitment256 is a commitment scheme that takes a 256-bit input.
pub type PedersenCommitment256<E> = PedersenCommitment<E, 2, 128>;
/// PedersenCommitment512 is a commitment scheme that takes a 512-bit input.
pub type PedersenCommitment512<E> = PedersenCommitment<E, 4, 128>;
/// PedersenCommitment1024 is a commitment scheme that takes a 1024-bit input.
pub type PedersenCommitment1024<E> = PedersenCommitment<E, 8, 128>;

/// PedersenCommitment is an additively-homomorphic commitment scheme that takes a variable-length
/// input.
pub struct PedersenCommitment<E: Environment, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> {
    /// The underlying Pedersen gadget, used to produce hashes of input bits.
    pedersen_gadget: Pedersen<E, NUM_WINDOWS, WINDOW_SIZE>,
    /// A vector of random bases, used for computing the commitment.
    random_base: Vec<Group<E>>,
}

impl<E: Environment, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>
    PedersenCommitment<E, NUM_WINDOWS, WINDOW_SIZE>
{
    /// Initializes a new instance of the Pedersen commitment gadget with the given setup message.
    pub fn setup(message: &str) -> Self {
        let pedersen_gadget = Pedersen::setup(message);

        // Compute the random base
        let (generator, _, _) = hash_to_curve(&format!("{message} for random base"));
        let mut base = Group::constant(generator);

        let num_scalar_bits = E::ScalarField::size_in_bits();
        let mut random_base = Vec::with_capacity(num_scalar_bits);
        for _ in 0..num_scalar_bits {
            random_base.push(base.clone());
            base = base.double();
        }

        Self { pedersen_gadget, random_base }
    }

    /// Returns the Pedersen commitment of the given input with the given randomness
    /// as an affine group element.
    pub fn commit(&self, input: &[Boolean<E>], randomness: &[Boolean<E>]) -> Group<E> {
        let hash = self.pedersen_gadget.hash_uncompressed(input);

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
    use snarkvm_curves::{AffineCurve, ProjectiveCurve};
    use snarkvm_utilities::{test_rng, ToBits, UniformRand};

    const ITERATIONS: usize = 10;
    const MESSAGE: &str = "PedersenCommitmentCircuit0";
    const WINDOW_SIZE_MULTIPLIER: usize = 8;

    type Projective = <<Circuit as Environment>::Affine as AffineCurve>::Projective;
    type ScalarField = <Circuit as Environment>::ScalarField;

    fn check_setup<const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>(
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        for _ in 0..ITERATIONS {
            // Initialize the native Pedersen hash.
            let native = NativePedersenCommitment::<Projective, NUM_WINDOWS, WINDOW_SIZE>::setup(MESSAGE);

            Circuit::scope("Pedersen::setup", || {
                // Perform the setup operation.
                let circuit = PedersenCommitment::<Circuit, NUM_WINDOWS, WINDOW_SIZE>::setup(MESSAGE);
                assert_scope!(num_constants, num_public, num_private, num_constraints);

                // Check for equality of the random base.
                native.random_base.iter().zip_eq(circuit.random_base.iter()).for_each(|(expected, candidate)| {
                    assert_eq!(expected.to_affine(), candidate.eject_value());
                });
            });
        }
    }

    #[test]
    fn test_setup_constant() {
        // Set the number of windows, and modulate the window size.
        check_setup::<1, WINDOW_SIZE_MULTIPLIER>(785, 0, 0, 0);
        check_setup::<1, { 2 * WINDOW_SIZE_MULTIPLIER }>(809, 0, 0, 0);
        check_setup::<1, { 3 * WINDOW_SIZE_MULTIPLIER }>(833, 0, 0, 0);
        check_setup::<1, { 4 * WINDOW_SIZE_MULTIPLIER }>(857, 0, 0, 0);
        check_setup::<1, { 5 * WINDOW_SIZE_MULTIPLIER }>(881, 0, 0, 0);

        // Set the window size, and modulate the number of windows.
        check_setup::<1, WINDOW_SIZE_MULTIPLIER>(785, 0, 0, 0);
        check_setup::<2, WINDOW_SIZE_MULTIPLIER>(813, 0, 0, 0);
        check_setup::<3, WINDOW_SIZE_MULTIPLIER>(841, 0, 0, 0);
        check_setup::<4, WINDOW_SIZE_MULTIPLIER>(869, 0, 0, 0);
        check_setup::<5, WINDOW_SIZE_MULTIPLIER>(897, 0, 0, 0);
    }

    fn check_commitment<const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>(
        mode: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        // Initialize the Pedersen hash.
        let native = NativePedersenCommitment::<Projective, NUM_WINDOWS, WINDOW_SIZE>::setup(MESSAGE);
        let circuit = PedersenCommitment::<Circuit, NUM_WINDOWS, WINDOW_SIZE>::setup(MESSAGE);
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
