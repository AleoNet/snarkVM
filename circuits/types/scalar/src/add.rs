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
use snarkvm_circuits_environment::Count;
use snarkvm_utilities::{FromBytes, ToBytes};

impl<E: Environment> Add<Scalar<E>> for Scalar<E> {
    type Output = Scalar<E>;

    fn add(self, other: Scalar<E>) -> Self::Output {
        self + &other
    }
}

impl<E: Environment> Add<Scalar<E>> for &Scalar<E> {
    type Output = Scalar<E>;

    fn add(self, other: Scalar<E>) -> Self::Output {
        self + &other
    }
}

impl<E: Environment> Add<&Scalar<E>> for Scalar<E> {
    type Output = Scalar<E>;

    fn add(self, other: &Scalar<E>) -> Self::Output {
        &self + other
    }
}

impl<E: Environment> Add<&Scalar<E>> for &Scalar<E> {
    type Output = Scalar<E>;

    fn add(self, other: &Scalar<E>) -> Self::Output {
        let mut result = self.clone();
        result += other;
        result
    }
}

impl<E: Environment> AddAssign<Scalar<E>> for Scalar<E> {
    fn add_assign(&mut self, other: Scalar<E>) {
        *self += &other;
    }
}

impl<E: Environment> AddAssign<&Scalar<E>> for Scalar<E> {
    fn add_assign(&mut self, other: &Scalar<E>) {
        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the sum and set the new constant in `self`.
            *self = witness!(|self, other| self + other);
        } else {
            // Instead of adding the bits of `self` and `other` directly, the scalars are
            // converted into a field elements, and summed, before converting back to scalars.
            // Note: This is safe as the base field is larger than the scalar field.
            let sum = self.to_field() + other.to_field();

            // Extract the scalar field bits from the field element, with a carry bit.
            // (For advanced users) This operation saves us 2 private variables and 2 constraints.
            let bits_le = sum.to_lower_bits_le(E::ScalarField::size_in_bits() + 1);

            // Recover the sanitized (truncated) sum on the base field.
            // (For advanced users) This operation saves us 2 private variables and 2 constraints.
            let sum = Field::from_bits_le(&bits_le);

            // Initialize the scalar field modulus as a constant base field variable.
            //
            // Note: We are reconstituting the scalar field into a base field here in order to
            // compute the difference between the sum and modulus. This is safe as the scalar field modulus
            // is less that the base field modulus, and thus will always fit in a base field element.
            let modulus = Field::constant(match E::ScalarField::modulus().to_bytes_le() {
                Ok(modulus_bytes) => match E::BaseField::from_bytes_le(&modulus_bytes) {
                    Ok(modulus) => modulus,
                    Err(error) => E::halt(format!("Failed to load the scalar modulus as a constant: {error}")),
                },
                Err(error) => E::halt(format!("Failed to retrieve the scalar modulus as bytes: {error}")),
            });

            // Determine the wrapping sum, by computing the difference between the sum and modulus, if `sum` < `modulus`.
            let wrapping_sum = Ternary::ternary(&sum.is_less_than(&modulus), &sum, &(&sum - &modulus));

            // Set the sum of `self` and `other`, in `self`.
            // Note: Direct indexing the slice here is safe as the scalar field smaller than the base field.
            *self = Scalar { bits_le: wrapping_sum.to_bits_le()[0..E::ScalarField::size_in_bits()].to_vec() };
        }
    }
}

impl<E: Environment> CountForOp<dyn Add<Scalar<E>, Output = Scalar<E>>> for Scalar<E> {
    type Case = (Mode, Mode);

    fn count(input: &Self::Case) -> Count {
        match (input.0, input.1) {
            (Mode::Constant, Mode::Constant) => Count::exact(251, 0, 0, 0),
            (_, _) => Count::exact(254, 0, 1021, 1023),
        }
    }
}

impl<E: Environment> OutputModeForOp<dyn Add<Scalar<E>, Output = Scalar<E>>> for Scalar<E> {
    type Case = (Mode, Mode);

    fn output_mode(input: &Self::Case) -> Mode {
        match (input.0, input.1) {
            (Mode::Constant, Mode::Constant) => Mode::Constant,
            (_, _) => Mode::Private,
        }
    }
}

impl<E: Environment> MetadataForOp<dyn Add<Scalar<E>, Output = Scalar<E>>> for Scalar<E> {}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::{assert_count, assert_output_mode, Circuit};
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: usize = 128;

    #[rustfmt::skip]
    fn check_add(
        name: &str,
        first: <Circuit as Environment>::ScalarField,
        second: <Circuit as Environment>::ScalarField,
        mode_a: Mode,
        mode_b: Mode,
    ) {
        let a = Scalar::<Circuit>::new(mode_a, first);
        let b = Scalar::<Circuit>::new(mode_b, second);
        let case = format!("({} + {})", a.eject_value(), b.eject_value());
        let expected = first + second;

        Circuit::scope(name, || {
            let candidate = a + b;
            assert_eq!(expected, candidate.eject_value(), "{}", case);
            assert_count!(Scalar<Circuit>, Add<Scalar<Circuit>, Output=Scalar<Circuit>>, &(mode_a, mode_b));
            assert_output_mode!(candidate, Scalar<Circuit>, Add<Scalar<Circuit>, Output=Scalar<Circuit>>, &(mode_a, mode_b));
        });
    }

    #[rustfmt::skip]
    fn run_test(
        mode_a: Mode,
        mode_b: Mode,
    ) {
        for i in 0..ITERATIONS {
            let first = UniformRand::rand(&mut test_rng());
            let second = UniformRand::rand(&mut test_rng());

            let name = format!("Add: {} + {} {}", mode_a, mode_b, i);
            check_add(&name, first, second, mode_a, mode_b);

            let name = format!("Add: {} + {} {} (commutative)", mode_a, mode_b, i);
            check_add(&name, second, first, mode_a, mode_b);
        }
    }

    #[test]
    fn test_scalar_constant_plus_constant() {
        run_test(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_scalar_constant_plus_public() {
        run_test(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_scalar_constant_plus_private() {
        run_test(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_scalar_public_plus_constant() {
        run_test(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_scalar_private_plus_constant() {
        run_test(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_scalar_public_plus_public() {
        run_test(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_scalar_public_plus_private() {
        run_test(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_scalar_private_plus_public() {
        run_test(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_scalar_private_plus_private() {
        run_test(Mode::Private, Mode::Private);
    }
}
