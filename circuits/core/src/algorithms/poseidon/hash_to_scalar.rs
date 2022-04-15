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

impl<E: Environment> HashToScalar for Poseidon<E> {
    type Input = Field<E>;
    type Scalar = Scalar<E>;

    /// Returns a scalar from hashing the input.
    /// This method uses truncation (up to data bits) to project onto the scalar field.
    #[inline]
    fn hash_to_scalar(&self, input: &[Self::Input]) -> Self::Scalar {
        // Hash the input to the base field.
        let output = self.hash(input);

        // Truncate the output to the size in data bits (1 bit less than the MODULUS) of the scalar.
        // Slicing here is safe as the base field is larger than the scalar field.
        Scalar::from_bits_le(&output.to_bits_le()[..E::ScalarField::size_in_data_bits()])
    }
}

impl<E: Environment> Count<dyn HashToScalar<Input = Field<E>, Scalar = Field<E>>> for Poseidon<E> {
    type Case = ();

    fn count(_parameter: &Self::Case) -> CircuitCount {
        todo!()
    }
}

impl<E: Environment> OutputMode<dyn HashToScalar<Input = Field<E>, Scalar = Field<E>>> for Poseidon<E> {
    type Case = ();

    fn output_mode(_input: &Self::Case) -> Mode {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_algorithms::crypto_hash::Poseidon as NativePoseidon;
    use snarkvm_circuits_types::environment::Circuit;
    use snarkvm_utilities::{test_rng, FromBits, ToBits, UniformRand};

    const ITERATIONS: usize = 10;

    fn check_hash_to_scalar(
        mode: Mode,
        num_inputs: usize,
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

            // Compute the native hash to scalar.
            let expected = {
                // Use Poseidon as a random oracle.
                let output = native_poseidon.evaluate(&native_input);

                // Truncate the output to CAPACITY bits (1 bit less than MODULUS_BITS) in the scalar field.
                let mut bits = output.to_bits_le();
                bits.resize(<Circuit as Environment>::ScalarField::size_in_data_bits(), false);

                // Output the scalar field.
                let biginteger = <<Circuit as Environment>::ScalarField as PrimeField>::BigInteger::from_bits_le(&bits);
                match <<Circuit as Environment>::ScalarField as PrimeField>::from_repr(biginteger) {
                    // We know this case will always work, because we truncate the output to CAPACITY bits in the scalar field.
                    Some(scalar) => scalar,
                    _ => panic!("Failed to hash input into scalar field"),
                }
            };

            // Compute the circuit hash.
            Circuit::scope(format!("Poseidon {mode} {i}"), || {
                let candidate = poseidon.hash_to_scalar(&input);
                assert_eq!(expected, candidate.eject_value());
                let case = format!("(mode = {mode}, num_inputs = {num_inputs})");
                assert_scope!(case, num_constants, num_public, num_private, num_constraints);
            });
        }
    }

    #[test]
    fn test_hash_to_scalar_constant() {
        for num_inputs in 0..=RATE {
            check_hash_to_scalar(Mode::Constant, num_inputs, 253, 0, 0, 0);
        }
    }

    #[test]
    fn test_hash_to_scalar_public() {
        check_hash_to_scalar(Mode::Public, 0, 253, 0, 0, 0);
        check_hash_to_scalar(Mode::Public, 1, 0, 0, 588, 589);
        check_hash_to_scalar(Mode::Public, 2, 0, 0, 593, 594);
        check_hash_to_scalar(Mode::Public, 3, 0, 0, 598, 599);
        check_hash_to_scalar(Mode::Public, 4, 0, 0, 603, 604);
        check_hash_to_scalar(Mode::Public, 5, 0, 0, 958, 959);
        check_hash_to_scalar(Mode::Public, 6, 0, 0, 958, 959);
        check_hash_to_scalar(Mode::Public, 7, 0, 0, 958, 959);
        check_hash_to_scalar(Mode::Public, 8, 0, 0, 958, 959);
        check_hash_to_scalar(Mode::Public, 9, 0, 0, 1313, 1314);
        check_hash_to_scalar(Mode::Public, 10, 0, 0, 1313, 1314);
    }

    #[test]
    fn test_hash_to_scalar_private() {
        check_hash_to_scalar(Mode::Private, 0, 253, 0, 0, 0);
        check_hash_to_scalar(Mode::Private, 1, 0, 0, 588, 589);
        check_hash_to_scalar(Mode::Private, 2, 0, 0, 593, 594);
        check_hash_to_scalar(Mode::Private, 3, 0, 0, 598, 599);
        check_hash_to_scalar(Mode::Private, 4, 0, 0, 603, 604);
        check_hash_to_scalar(Mode::Private, 5, 0, 0, 958, 959);
        check_hash_to_scalar(Mode::Private, 6, 0, 0, 958, 959);
        check_hash_to_scalar(Mode::Private, 7, 0, 0, 958, 959);
        check_hash_to_scalar(Mode::Private, 8, 0, 0, 958, 959);
        check_hash_to_scalar(Mode::Private, 9, 0, 0, 1313, 1314);
        check_hash_to_scalar(Mode::Private, 10, 0, 0, 1313, 1314);
    }
}
