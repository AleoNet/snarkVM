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

impl<E: Environment, I: PrimitiveUnsignedInteger, const SIZE: usize> Neg for Unsigned<E, I, SIZE> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        let value = self.eject_value().wrapping_neg();

        if self.is_constant() {
            return Unsigned::new(Mode::Constant, value);
        }

        let flipped = Unsigned::from_bits(self.bits_le.iter().map(|bit| !bit).collect());
        let mut one = Unsigned::new(Mode::Constant, I::one());
        let result = flipped.add(one);

        // TODO (@pranav) Is this check necessary? It does not seem to be done in the corresponding
        //   gadget implementation.
        // Check that the computed result is correct
        for i in 0..SIZE {
            let mask = I::one() << i;
            let value_bit = Boolean::<E>::new(Mode::Private, value & mask == mask);
            value_bit.is_eq(&result.bits_le[i]);
        }

        result
    }
}

impl<E: Environment, I: PrimitiveUnsignedInteger, const SIZE: usize> Neg for &Unsigned<E, I, SIZE> {
    type Output = Unsigned<E, I, SIZE>;

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
        expected: u64,
        candidate_input: Unsigned<Circuit, u64, 64>,
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
            let value: u64 = UniformRand::rand(&mut thread_rng());
            let expected = value.wrapping_neg();

            let candidate_input = Unsigned::<Circuit, u64, 64>::new(Mode::Constant, value);
            check_neg(&format!("NEG Constant {}", i), expected, candidate_input, 0, 0, 0, 0);
        }
    }

    #[test]
    fn test_neg_public() {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let value: u64 = UniformRand::rand(&mut thread_rng());
            let expected = value.wrapping_neg();

            let candidate_input = Unsigned::<Circuit, u64, 64>::new(Mode::Public, value);
            check_neg(&format!("NEG Public {}", i), expected, candidate_input, 0, 0, 0, 0);
        }
    }

    #[test]
    fn test_neg_private() {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let value: u64 = UniformRand::rand(&mut thread_rng());
            let expected = value.wrapping_neg();

            let candidate_input = Unsigned::<Circuit, u64, 64>::new(Mode::Private, value);
            check_neg(&format!("NEG Private {}", i), expected, candidate_input, 0, 0, 0, 0);
        }
    }
}
