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

impl<E: Environment> LessThan<Scalar<E>> for Scalar<E> {
    type Output = Boolean<E>;

    /// Returns `true` if `self` is less than `other`.
    fn is_less_than(&self, other: &Self) -> Self::Output {
        let mut is_less_than = Boolean::constant(false);
        let mut are_previous_bits_equal = Boolean::constant(true);

        // Initialize an iterator over `self` and `other` from MSB to LSB.
        let bits_be = self.bits_le.iter().rev().zip_eq(other.bits_le.iter().rev());

        for (index, (self_bit, other_bit)) in bits_be.enumerate() {
            // Determine if `self` is less than `other` up to the `index`-th bit.
            is_less_than |= &are_previous_bits_equal & (!self_bit & other_bit);

            // Skip the update to the LSB, as this boolean is subsequently discarded.
            if index != self.bits_le.len() - 1 {
                are_previous_bits_equal &= self_bit.is_equal(other_bit);
            }
        }

        is_less_than
    }
}

impl<E: Environment> Metadata<dyn LessThan<Scalar<E>, Output = Boolean<E>>> for Scalar<E> {
    type Case = (CircuitType<Self>, CircuitType<Self>);
    type OutputType = CircuitType<Boolean<E>>;

    fn count(case: &Self::Case) -> Count {
        match case {
            (CircuitType::Constant(_), CircuitType::Constant(_)) => Count::is(0, 0, 0, 0),
            (CircuitType::Public, CircuitType::Constant(_)) | (CircuitType::Constant(_), CircuitType::Public) => {
                Count::is(0, 473, 0, 473)
            }
            (CircuitType::Private, CircuitType::Constant(_)) | (CircuitType::Constant(_), CircuitType::Private) => {
                Count::is(0, 0, 503, 503)
            }
            _ => Count::is(0, 0, 1250, 1250),
        }
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        match case {
            (CircuitType::Constant(a), CircuitType::Constant(b)) => {
                CircuitType::from(a.circuit().is_less_than(b.circuit()))
            }
            _ => CircuitType::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: u64 = 100;

    fn check_is_less_than(mode_a: Mode, mode_b: Mode) {
        for i in 0..ITERATIONS {
            // Sample a random element `a`.
            let expected_a: <Circuit as Environment>::ScalarField = UniformRand::rand(&mut test_rng());
            let candidate_a = Scalar::<Circuit>::new(mode_a, expected_a);

            // Sample a random element `b`.
            let expected_b: <Circuit as Environment>::ScalarField = UniformRand::rand(&mut test_rng());
            let candidate_b = Scalar::<Circuit>::new(mode_b, expected_b);

            // Perform the less than comparison.
            Circuit::scope(&format!("{} {} {}", mode_a, mode_b, i), || {
                let candidate = candidate_a.is_less_than(&candidate_b);
                assert_eq!(expected_a < expected_b, candidate.eject_value());

                let case = (CircuitType::from(candidate_a), CircuitType::from(candidate_b));
                assert_count!(LessThan(Scalar, Scalar) => Boolean, &case);
                assert_output_type!(LessThan(Scalar, Scalar) => Boolean, case, candidate);
            });
            Circuit::reset();
        }
    }

    #[test]
    fn test_constant_is_less_than_constant() {
        check_is_less_than(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_constant_is_less_than_public() {
        check_is_less_than(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_constant_is_less_than_private() {
        check_is_less_than(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_public_is_less_than_constant() {
        check_is_less_than(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_public_is_less_than_public() {
        check_is_less_than(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_public_is_less_than_private() {
        check_is_less_than(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_private_is_less_than_constant() {
        check_is_less_than(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_private_is_less_than_public() {
        check_is_less_than(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_private_is_less_than_private() {
        check_is_less_than(Mode::Private, Mode::Private);
    }
}
