// Copyright (C) 2019-2021 Aleo Systems Inc.
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
use crate::RippleCarryAdder;

impl<E: Environment, I: PrimitiveSignedInteger, const SIZE: usize> Neg for Signed<E, I, SIZE> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        // Determine the variable mode.
        let mode = match self.is_constant() && other.is_constant() {
            true => Mode::Constant,
            false => Mode::Private,
        };

        if mode.is_constant() {
            return Signed::new(mode, self.eject_value().wrapping_neg());
        }

        let flipped = Signed::from_bits(self.bits_le.iter().map(|bit| !bit).collect());
        let mut one = Signed::new(Mode::Constant, I::one());

        flipped.add(one)
    }
}

impl<E: Environment, I: PrimitiveSignedInteger, const SIZE: usize> Neg for &Signed<E, I, SIZE> {
    type Output = Signed<E, I, SIZE>;

    fn neg(self) -> Self::Output {
        -(self.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

    const ITERATIONS: usize = 100;

    fn check_neg(
        name: &str,
        expected: i64,
        candidate_input: Signed<Circuit, i64, 64>,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, |scope| {
            let candidate_output = -candidate_input;
            assert_eq!(expected, candidate_output.eject_value());

            // assert_eq!(num_constants, scope.num_constants_in_scope());
            // assert_eq!(num_public, scope.num_public_in_scope());
            // assert_eq!(num_private, scope.num_private_in_scope());
            // assert_eq!(num_constraints, scope.num_constraints_in_scope());
            assert!(Circuit::is_satisfied());
        });
    }

    #[test]
    fn test_neg_constant() {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let value: i64 = UniformRand::rand(&mut thread_rng());
            let expected = match value.checked_neg() {
                Some(expected) => expected,
                None => continue,
            };

            let candidate_input = Signed::<Circuit, i64, 64>::new(Mode::Constant, value);
            check_neg(&format!("NEG Constant {}", i), expected, candidate_input, 0, 0, 0, 0);
        }
    }

    #[test]
    fn test_neg_public() {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let value: i64 = UniformRand::rand(&mut thread_rng());
            let expected = match value.checked_neg() {
                Some(expected) => expected,
                None => continue,
            };

            let candidate_input = Signed::<Circuit, i64, 64>::new(Mode::Public, value);
            check_neg(&format!("NEG Public {}", i), expected, candidate_input, 0, 0, 0, 0);
        }
    }

    #[test]
    fn test_neg_private() {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let value: i64 = UniformRand::rand(&mut thread_rng());
            let expected = match value.checked_neg() {
                Some(expected) => expected,
                None => continue,
            };

            let candidate_input = Signed::<Circuit, i64, 64>::new(Mode::Private, value);
            check_neg(&format!("NEG Private {}", i), expected, candidate_input, 0, 0, 0, 0);
        }
    }
}
