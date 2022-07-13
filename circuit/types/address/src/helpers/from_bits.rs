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

impl<E: Environment> FromBits for Address<E> {
    type Boolean = Boolean<E>;

    /// Initializes an address from a list of little-endian bits *without* trailing zeros.
    fn from_bits_le(bits_le: &[Self::Boolean]) -> Self {
        Self(Group::from_bits_le(bits_le))
    }

    /// Initializes an address from a list of big-endian bits *without* leading zeros.
    fn from_bits_be(bits_be: &[Self::Boolean]) -> Self {
        Self(Group::from_bits_be(bits_be))
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    const ITERATIONS: u64 = 100;

    fn check_from_bits_le(mode: Mode, num_constants: u64, num_public: u64, num_private: u64, num_constraints: u64) {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected: console::Group<<Circuit as Environment>::Network> = Uniform::rand(&mut test_rng());
            let candidate = Group::<Circuit>::new(mode, expected).to_bits_le();

            Circuit::scope(&format!("{} {}", mode, i), || {
                let candidate = Address::<Circuit>::from_bits_le(&candidate);
                assert_eq!(expected, *candidate.eject_value());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
            Circuit::reset();
        }
    }

    fn check_from_bits_be(mode: Mode, num_constants: u64, num_public: u64, num_private: u64, num_constraints: u64) {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected: console::Group<<Circuit as Environment>::Network> = Uniform::rand(&mut test_rng());
            let candidate = Group::<Circuit>::new(mode, expected).to_bits_be();

            Circuit::scope(&format!("{} {}", mode, i), || {
                let candidate = Address::<Circuit>::from_bits_be(&candidate);
                assert_eq!(expected, *candidate.eject_value());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
            Circuit::reset();
        }
    }

    #[test]
    fn test_from_bits_le_constant() {
        check_from_bits_le(Mode::Constant, 3, 0, 0, 0);
    }

    #[test]
    fn test_from_bits_le_public() {
        check_from_bits_le(Mode::Public, 2, 0, 255, 256);
    }

    #[test]
    fn test_from_bits_le_private() {
        check_from_bits_le(Mode::Private, 2, 0, 255, 256);
    }

    #[test]
    fn test_from_bits_be_constant() {
        check_from_bits_be(Mode::Constant, 3, 0, 0, 0);
    }

    #[test]
    fn test_from_bits_be_public() {
        check_from_bits_be(Mode::Public, 2, 0, 255, 256);
    }

    #[test]
    fn test_from_bits_be_private() {
        check_from_bits_be(Mode::Private, 2, 0, 255, 256);
    }
}
