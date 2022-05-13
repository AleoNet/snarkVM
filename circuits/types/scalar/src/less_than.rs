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
        let (left, right) = case.clone();

        let mut total_count = Count::zero();

        let mut is_less_than_type = CircuitType::from(Boolean::constant(false));
        let mut are_previous_bits_equal_type = CircuitType::from(Boolean::constant(true));

        // Get the little endian bits of self and other. We do not need to add this to the count, as it is free.
        let self_bits_le_type = output_type!(Scalar<E>, ToBitsLE<Boolean = Boolean<E>>, left);
        let other_bits_le_type = output_type!(Scalar<E>, ToBitsLE<Boolean = Boolean<E>>, right);

        let bits_be = self_bits_le_type.into_iter().rev().zip_eq(other_bits_le_type.into_iter().rev());
        let length = bits_be.len();

        for (index, (self_bit, other_bit)) in bits_be.enumerate() {
            // Compute the cost and output type of `!self_bit`.
            let case = self_bit.clone();
            total_count = total_count + count!(Boolean<E>, Not<Output = Boolean<E>>, &case);
            let not_self_bit_type = output_type!(Boolean<E>, Not<Output = Boolean<E>>, case);

            // Compute the cost of and output type of `!self_bit & other_bit`.
            let case = (not_self_bit_type, other_bit.clone());
            total_count = total_count + count!(Boolean<E>, BitAnd<Boolean<E>, Output = Boolean<E>>, &case);
            let not_self_and_other_bit_type = output_type!(Boolean<E>, BitAnd<Boolean<E>, Output = Boolean<E>>, case);

            // Compute the cost of `are_previous_bits_equal & !self_bit & other_bit`.
            let case = (are_previous_bits_equal_type.clone(), not_self_and_other_bit_type);
            total_count = total_count + count!(Boolean<E>, BitAnd<Boolean<E>, Output = Boolean<E>>, &case);
            let are_previous_bits_equal_and_not_self_and_other_bit_type =
                output_type!(Boolean<E>, BitAnd<Boolean<E>, Output = Boolean<E>>, case);

            // Compute the cost of `less_than |= are_previous_bits_equal & (!self_bit & other_bit)`.
            let case = (is_less_than_type, are_previous_bits_equal_and_not_self_and_other_bit_type);
            total_count = total_count + count!(Boolean<E>, BitOr<Boolean<E>, Output = Boolean<E>>, &case);
            is_less_than_type = output_type!(Boolean<E>, BitOr<Boolean<E>, Output = Boolean<E>>, case);

            // Skip the update to the LSB, as this boolean is subsequently discarded.
            if index != length - 1 {
                // Compute the cost and output type of `self_bit.is_equal(other_bit)`.
                let case = (self_bit, other_bit);
                total_count = total_count + count!(Boolean<E>, Equal<Boolean<E>, Output = Boolean<E>>, &case);
                let self_bit_is_equal_other_bit_type =
                    output_type!(Boolean<E>, Equal<Boolean<E>, Output = Boolean<E>>, case);

                // Compute the cost and output type `are_previous_bits_equal & self_bit.is_equal(other_bit)`.
                let case = (are_previous_bits_equal_type, self_bit_is_equal_other_bit_type);
                total_count = total_count + count!(Boolean<E>, BitAnd<Boolean<E>, Output = Boolean<E>>, &case);
                are_previous_bits_equal_type = output_type!(Boolean<E>, BitAnd<Boolean<E>, Output = Boolean<E>>, case);
            }
        }
        total_count
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        let (left, right) = case;

        let mut is_less_than_type = CircuitType::from(Boolean::constant(false));
        let mut are_previous_bits_equal_type = CircuitType::from(Boolean::constant(true));

        // Get the little endian bits of self and other. We do not need to add this to the count, as it is free.
        let self_bits_le_type = output_type!(Scalar<E>, ToBitsLE<Boolean = Boolean<E>>, left);
        let other_bits_le_type = output_type!(Scalar<E>, ToBitsLE<Boolean = Boolean<E>>, right);

        let bits_be = self_bits_le_type.into_iter().rev().zip_eq(other_bits_le_type.into_iter().rev());
        let length = bits_be.len();

        for (index, (self_bit, other_bit)) in bits_be.enumerate() {
            // Compute the output type of `!self_bit`.
            let case = self_bit.clone();
            let not_self_bit_type = output_type!(Boolean<E>, Not<Output = Boolean<E>>, case);

            // Compute the output type of `!self_bit & other_bit`.
            let case = (not_self_bit_type, other_bit.clone());
            let not_self_and_other_bit_type = output_type!(Boolean<E>, BitAnd<Boolean<E>, Output = Boolean<E>>, case);

            // Compute the output type of `are_previous_bits_equal & !self_bit & other_bit`.
            let case = (are_previous_bits_equal_type.clone(), not_self_and_other_bit_type);
            let are_previous_bits_equal_and_not_self_and_other_bit_type =
                output_type!(Boolean<E>, BitAnd<Boolean<E>, Output = Boolean<E>>, case);

            // Compute the output type of `less_than |= are_previous_bits_equal & !self_bit & other_bit`.
            let case = (is_less_than_type, are_previous_bits_equal_and_not_self_and_other_bit_type);
            is_less_than_type = output_type!(Boolean<E>, BitOr<Boolean<E>, Output = Boolean<E>>, case);

            // Skip the update to the LSB, as this boolean is subsequently discarded.
            if index != length - 1 {
                let case = (self_bit, other_bit);
                let self_bit_is_equal_other_bit_type =
                    output_type!(Boolean<E>, Equal<Boolean<E>, Output = Boolean<E>>, case);

                let case = (are_previous_bits_equal_type, self_bit_is_equal_other_bit_type);
                are_previous_bits_equal_type = output_type!(Boolean<E>, BitAnd<Boolean<E>, Output = Boolean<E>>, case);
            }
        }
        is_less_than_type
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
