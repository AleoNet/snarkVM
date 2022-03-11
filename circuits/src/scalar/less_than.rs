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

use itertools::Itertools;

impl<E: Environment> LessThan<Scalar<E>> for Scalar<E> {
    type Boolean = Boolean<E>;

    ///
    /// Returns `true` if `self` is less than `other`.
    ///
    fn is_less_than(&self, other: &Self) -> Self::Boolean {
        // let (mut is_less_than, mut are_previous_bits_equal) = (self.msb() & !other.msb(), self.msb().is_eq(other.msb());
        //
        // // Compare the remaining bits.
        // for (self_bit, other_bit) in self.bits_le.iter().rev().zip_eq(other.bits_le.iter().rev()).skip(1) {
        //     is_less_than |= &are_previous_bits_equal & !self_bit & other_bit;
        //     are_previous_bits_equal &= self_bit.is_eq(other_bit);
        // }
        //
        // is_less_than

        let mut is_less_than = Boolean::new(Mode::Constant, false);
        let mut are_previous_bits_equal = Boolean::new(Mode::Constant, true);

        // Initialize an iterator over `self` and `other` from MSB to LSB.
        let bits_be = self.bits_le.iter().rev().zip_eq(other.bits_le.iter().rev());

        for (index, (self_bit, other_bit)) in bits_be.enumerate() {
            // Determine if `self` is less than `other` up to the `index`-th bit.
            is_less_than |= &are_previous_bits_equal & (!self_bit & other_bit);

            // Skip the update to the LSB, as this boolean is subsequently discarded.
            if index != self.bits_le.len() - 1 {
                are_previous_bits_equal &= self_bit.is_eq(other_bit);
            }
        }

        is_less_than
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{assert_circuit, Circuit};
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

    const ITERATIONS: usize = 100;

    fn check_less_than(
        mode: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        for i in 0..ITERATIONS {
            // Sample a random element `a`.
            let expected_a: <Circuit as Environment>::ScalarField = UniformRand::rand(&mut thread_rng());
            let candidate_a = Scalar::<Circuit>::new(mode, expected_a);

            // Sample a random element `b`.
            let expected_b: <Circuit as Environment>::ScalarField = UniformRand::rand(&mut thread_rng());
            let candidate_b = Scalar::<Circuit>::new(mode, expected_b);

            // Perform the less than comparison.
            Circuit::scoped(&format!("{} {}", mode, i), || {
                let candidate = candidate_a.is_less_than(&candidate_b);
                assert_eq!(expected_a < expected_b, candidate.eject_value());
                assert_circuit!(num_constants, num_public, num_private, num_constraints);
            });
            Circuit::reset();
        }
    }

    #[test]
    fn test_less_than_constant() {
        check_less_than(Mode::Constant, 2, 0, 0, 0);
    }

    #[test]
    fn test_less_than_public() {
        check_less_than(Mode::Public, 2, 0, 1250, 1250);
    }

    #[test]
    fn test_less_than_private() {
        check_less_than(Mode::Private, 2, 0, 1250, 1250);
    }
}
