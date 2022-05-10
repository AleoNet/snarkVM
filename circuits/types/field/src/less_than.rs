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

impl<E: Environment> LessThan<Field<E>> for Field<E> {
    type Output = Boolean<E>;

    /// Returns `true` if `self` is less than `other`.
    fn is_less_than(&self, other: &Self) -> Self::Output {
        let mut is_less_than = Boolean::constant(false);
        let mut are_previous_bits_equal = Boolean::constant(true);

        // Initialize an iterator over `self` and `other` from MSB to LSB.
        let self_bits_be = self.to_bits_be();
        let other_bits_be = other.to_bits_be();
        let bits_be = self_bits_be.iter().zip_eq(&other_bits_be);

        for (index, (self_bit, other_bit)) in bits_be.enumerate() {
            // Determine if `self` is less than `other` up to the `index`-th bit.
            is_less_than |= &are_previous_bits_equal & (!self_bit & other_bit);

            // Skip the update to the LSB, as this boolean is subsequently discarded.
            if index != self_bits_be.len() - 1 {
                are_previous_bits_equal &= self_bit.is_equal(other_bit);
            }
        }

        is_less_than
    }
}

impl<E: Environment> Metadata<dyn LessThan<Field<E>, Output = Boolean<E>>> for Field<E> {
    type Case = (CircuitType<Self>, CircuitType<Self>);
    type OutputType = CircuitType<Boolean<E>>;

    fn count(case: &Self::Case) -> Count {
        match case {
            (CircuitType::Constant(_), CircuitType::Constant(_)) => Count::is(506, 0, 0, 0),
            (other_type, CircuitType::Constant(constant)) | (CircuitType::Constant(constant), other_type) => {
                todo!()
            }
            (_, _) => Count::is(0, 0, 1766, 1768),
        }
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        match case {
            (CircuitType::Constant(a), CircuitType::Constant(b)) => {
                CircuitType::from(a.circuit().is_less_than(b.circuit()))
            }
            (other_type, CircuitType::Constant(constant)) | (CircuitType::Constant(constant), other_type) => {
                // TODO: Finish this case.
                CircuitType::Private
            }
            (_, _) => CircuitType::Private,
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
            let expected_a: <Circuit as Environment>::BaseField = UniformRand::rand(&mut test_rng());
            let candidate_a = Field::<Circuit>::new(mode_a, expected_a);

            // Sample a random element `b`.
            let expected_b: <Circuit as Environment>::BaseField = UniformRand::rand(&mut test_rng());
            let candidate_b = Field::<Circuit>::new(mode_b, expected_b);

            // Perform the less than comparison.
            Circuit::scope(&format!("{} {} {}", mode_a, mode_b, i), || {
                let candidate = candidate_a.is_less_than(&candidate_b);
                assert_eq!(expected_a < expected_b, candidate.eject_value());

                let case = (CircuitType::from(candidate_a), CircuitType::from(candidate_b));
                assert_count!(LessThan(Field, Field) => Boolean, &case);
                assert_output_type!(LessThan(Field, Field) => Boolean, case, candidate);
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
    fn test_public_is_less_than_public() {
        check_is_less_than(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_public_is_less_than_private() {
        check_is_less_than(Mode::Public, Mode::Private);
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
