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

impl<E: Environment> FromBits for Affine<E> {
    type Boolean = Boolean<E>;

    /// Initializes a new group element from the x-coordinate as a list of little-endian bits *without* trailing zeros.
    fn from_bits_le(mode: Mode, bits_le: &[Self::Boolean]) -> Self {
        // Derive the x-coordinate for the affine group element.
        let x = BaseField::from_bits_le(mode, bits_le);
        // Recover the y-coordinate and return the affine group element.
        Self::from_x_coordinate(mode, x)
    }

    /// Initializes a new group element from the x-coordinate as a list of big-endian bits *without* leading zeros.
    fn from_bits_be(mode: Mode, bits_be: &[Self::Boolean]) -> Self {
        // Derive the x-coordinate for the affine group element.
        let x = BaseField::from_bits_be(mode, bits_be);
        // Recover the y-coordinate and return the affine group element.
        Self::from_x_coordinate(mode, x)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{assert_circuit, Circuit};
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

    const ITERATIONS: usize = 100;

    fn check_from_bits_le(
        mode: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let candidate =
                Affine::<Circuit>::new(mode, (expected.to_x_coordinate(), Some(expected.to_y_coordinate())))
                    .to_bits_le();

            Circuit::scoped(&format!("{} {}", mode, i), || {
                let candidate = Affine::<Circuit>::from_bits_le(mode, &candidate);
                assert_eq!(expected, candidate.eject_value());
                assert_circuit!(num_constants, num_public, num_private, num_constraints);
            });
        }
    }

    fn check_from_bits_be(
        mode: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let candidate =
                Affine::<Circuit>::new(mode, (expected.to_x_coordinate(), Some(expected.to_y_coordinate())))
                    .to_bits_be();

            Circuit::scoped(&format!("{} {}", mode, i), || {
                let candidate = Affine::<Circuit>::from_bits_be(mode, &candidate);
                assert_eq!(expected, candidate.eject_value());
                assert_circuit!(num_constants, num_public, num_private, num_constraints);
            });
        }
    }

    #[test]
    fn test_from_bits_le_constant() {
        check_from_bits_le(Mode::Constant, 5, 0, 0, 0);
    }

    #[test]
    fn test_from_bits_le_public() {
        check_from_bits_le(Mode::Public, 3, 2, 2, 4);
    }

    #[test]
    fn test_from_bits_le_private() {
        check_from_bits_le(Mode::Private, 3, 0, 4, 4);
    }

    #[test]
    fn test_from_bits_be_constant() {
        check_from_bits_be(Mode::Constant, 5, 0, 0, 0);
    }

    #[test]
    fn test_from_bits_be_public() {
        check_from_bits_be(Mode::Public, 3, 2, 2, 4);
    }

    #[test]
    fn test_from_bits_be_private() {
        check_from_bits_be(Mode::Private, 3, 0, 4, 4);
    }
}
