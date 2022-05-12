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
use std::cmp::max;

use snarkvm_utilities::BigInteger;

impl<E: Environment> Mul<Scalar<E>> for Group<E> {
    type Output = Group<E>;

    fn mul(self, other: Scalar<E>) -> Self::Output {
        self * &other
    }
}

impl<E: Environment> Mul<Scalar<E>> for &Group<E> {
    type Output = Group<E>;

    fn mul(self, other: Scalar<E>) -> Self::Output {
        self * &other
    }
}

impl<E: Environment> Mul<&Scalar<E>> for Group<E> {
    type Output = Group<E>;

    fn mul(self, other: &Scalar<E>) -> Self::Output {
        let mut output = self;
        output *= other;
        output
    }
}

impl<E: Environment> Mul<&Scalar<E>> for &Group<E> {
    type Output = Group<E>;

    fn mul(self, other: &Scalar<E>) -> Self::Output {
        (*self).clone() * other
    }
}

impl<E: Environment> Mul<Group<E>> for Scalar<E> {
    type Output = Group<E>;

    fn mul(self, other: Group<E>) -> Self::Output {
        other * &self
    }
}

impl<E: Environment> Mul<Group<E>> for &Scalar<E> {
    type Output = Group<E>;

    fn mul(self, other: Group<E>) -> Self::Output {
        &other * self
    }
}

impl<E: Environment> Mul<&Group<E>> for Scalar<E> {
    type Output = Group<E>;

    fn mul(self, other: &Group<E>) -> Self::Output {
        other * &self
    }
}

impl<E: Environment> Mul<&Group<E>> for &Scalar<E> {
    type Output = Group<E>;

    fn mul(self, other: &Group<E>) -> Self::Output {
        other * self
    }
}

impl<E: Environment> MulAssign<Scalar<E>> for Group<E> {
    fn mul_assign(&mut self, other: Scalar<E>) {
        *self *= &other;
    }
}

impl<E: Environment> MulAssign<&Scalar<E>> for Group<E> {
    fn mul_assign(&mut self, other: &Scalar<E>) {
        *self *= other.to_bits_be().as_slice();
    }
}

impl<E: Environment, const N: usize> Mul<[Boolean<E>; N]> for Group<E> {
    type Output = Group<E>;

    fn mul(self, other: [Boolean<E>; N]) -> Self::Output {
        self * &other[..]
    }
}

impl<E: Environment, const N: usize> Mul<[Boolean<E>; N]> for &Group<E> {
    type Output = Group<E>;

    fn mul(self, other: [Boolean<E>; N]) -> Self::Output {
        self * &other[..]
    }
}

impl<E: Environment> Mul<&[Boolean<E>]> for Group<E> {
    type Output = Group<E>;

    fn mul(self, other: &[Boolean<E>]) -> Self::Output {
        let mut output = self;
        output *= other;
        output
    }
}

impl<E: Environment> Mul<&[Boolean<E>]> for &Group<E> {
    type Output = Group<E>;

    fn mul(self, other: &[Boolean<E>]) -> Self::Output {
        (*self).clone() * other
    }
}

impl<E: Environment, const N: usize> Mul<Group<E>> for [Boolean<E>; N] {
    type Output = Group<E>;

    fn mul(self, other: Group<E>) -> Self::Output {
        other * &self[..]
    }
}

impl<E: Environment> Mul<Group<E>> for &[Boolean<E>] {
    type Output = Group<E>;

    fn mul(self, other: Group<E>) -> Self::Output {
        &other * self
    }
}

impl<E: Environment, const N: usize> Mul<&Group<E>> for [Boolean<E>; N] {
    type Output = Group<E>;

    fn mul(self, other: &Group<E>) -> Self::Output {
        other * &self[..]
    }
}

impl<E: Environment> Mul<&Group<E>> for &[Boolean<E>] {
    type Output = Group<E>;

    fn mul(self, other: &Group<E>) -> Self::Output {
        other * self
    }
}

impl<E: Environment, const N: usize> MulAssign<[Boolean<E>; N]> for Group<E> {
    fn mul_assign(&mut self, other: [Boolean<E>; N]) {
        *self *= &other[..];
    }
}

impl<E: Environment> MulAssign<&[Boolean<E>]> for Group<E> {
    #[allow(clippy::suspicious_op_assign_impl)]
    fn mul_assign(&mut self, other: &[Boolean<E>]) {
        let base = self.clone();

        let mut output = Group::zero();
        for bit in other.iter() {
            output = output.double();
            output = Group::ternary(bit, &(&base + &output), &output);
        }
        *self = output;
    }
}

impl<E: Environment> Metadata<dyn Mul<Scalar<E>, Output = Group<E>>> for Group<E> {
    type Case = (CircuitType<Self>, CircuitType<Scalar<E>>);
    type OutputType = CircuitType<Self>;

    fn count(case: &Self::Case) -> Count {
        let (left, right) = case.clone();
        let to_bits_be_count = count!(Scalar<E>, ToBitsBE<Boolean = Boolean<E>>, &right);
        let to_bits_be_type = output_type!(Scalar<E>, ToBitsBE<Boolean = Boolean<E>>, right);

        let zero_count = count!(Group<E>, Zero<Boolean = Boolean<E>>, &());
        let zero_type = output_type!(Group<E>, Zero<Boolean = Boolean<E>>, ());

        let mut output_count = to_bits_be_count + zero_count;
        let mut output_type = zero_type;

        for bit in to_bits_be_type {
            output_count = output_count + count!(Group<E>, Double<Output = Group<E>>, &output_type);
            output_type = output_type!(Group<E>, Double<Output = Group<E>>, output_type);

            let case = (left.clone(), output_type.clone());
            let sum_count = count!(Group<E>, Add<Group<E>, Output = Group<E>>, &case);
            let sum_output_type = output_type!(Group<E>, Add<Group<E>, Output = Group<E>>, case);

            let case = (bit, sum_output_type, output_type);
            output_count =
                output_count + sum_count + count!(Group<E>, Ternary<Boolean = Boolean<E>, Output = Group<E>>, &case);
            output_type = output_type!(Group<E>, Ternary<Boolean = Boolean<E>, Output = Group<E>>, case);
        }

        output_count
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        let (left, right) = case;
        let to_bits_be_output_type = output_type!(Scalar<E>, ToBitsBE<Boolean = Boolean<E>>, right);

        let zero_output_type = output_type!(Group<E>, Zero<Boolean = Boolean<E>>, ());

        let mut output_type = zero_output_type;

        for bit in to_bits_be_output_type {
            output_type = output_type!(Group<E>, Double<Output = Group<E>>, output_type);

            let case = (left.clone(), output_type.clone());
            let sum_output_type = output_type!(Group<E>, Add<Group<E>, Output = Group<E>>, case);

            let case = (bit, sum_output_type, output_type);
            output_type = output_type!(Group<E>, Ternary<Boolean = Boolean<E>, Output = Group<E>>, case)
        }

        output_type
    }
}

// TODO: Do we need Metadata implementations for other multiplication operations? And corresponding tests.

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_curves::ProjectiveCurve;
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: u64 = 100;

    fn check_mul(name: &str, expected: &<Circuit as Environment>::Affine, a: &Group<Circuit>, b: &Scalar<Circuit>) {
        Circuit::scope(name, || {
            let candidate = a * b;
            assert_eq!(*expected, candidate.eject_value(), "({} * {})", a.eject_value(), b.eject_value());

            let case = (CircuitType::from(a), CircuitType::from(b));
            assert_count!(Mul(Group, Scalar) => Group, &case);
            assert_output_type!(Mul(Group, Scalar) => Group, case, candidate);
        });
        Circuit::reset();
    }

    fn check_mul_assign(
        name: &str,
        expected: &<Circuit as Environment>::Affine,
        a: &Group<Circuit>,
        b: &Scalar<Circuit>,
    ) {
        Circuit::scope(name, || {
            let mut candidate = a.clone();
            candidate *= b;
            assert_eq!(*expected, candidate.eject_value(), "({} * {})", a.eject_value(), b.eject_value());

            let case = (CircuitType::from(a), CircuitType::from(b));
            assert_count!(Mul(Group, Scalar) => Group, &case);
            assert_output_type!(Mul(Group, Scalar) => Group, case, candidate);
        });
        Circuit::reset();
    }

    fn run_test(mode_a: Mode, mode_b: Mode) {
        for i in 0..ITERATIONS {
            let base: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());
            let scalar: <Circuit as Environment>::ScalarField = UniformRand::rand(&mut test_rng());

            let expected = (base * scalar).into();
            let a = Group::<Circuit>::new(mode_a, base);
            let b = Scalar::<Circuit>::new(mode_b, scalar);

            let name = format!("Mul: a * b {}", i);
            check_mul(&name, &expected, &a, &b);
            let name = format!("MulAssign: a * b {}", i);
            check_mul_assign(&name, &expected, &a, &b);

            // Check zero cases.
            let affine_zero = <Circuit as Environment>::Affine::zero();
            let scalar_field_zero = <Circuit as Environment>::ScalarField::zero();
            let scalar_field_one = <Circuit as Environment>::ScalarField::one();

            let group_zero = Group::<Circuit>::new(mode_a, affine_zero);
            let scalar_zero = Scalar::<Circuit>::new(mode_b, scalar_field_zero);
            let scalar_one = Scalar::<Circuit>::new(mode_b, scalar_field_one);

            let name = format!("ZeroScalar: a * 0 {}", i);
            check_mul(&name, &affine_zero, &a, &scalar_zero);
            let name = format!("ZeroScalarAssign: a * 0 {}", i);
            check_mul_assign(&name, &affine_zero, &a, &scalar_zero);
            let name = format!("OneScalar: a * 1 {}", i);
            check_mul(&name, &base, &a, &scalar_one);
            let name = format!("OneScalarAssign: a * 1 {}", i);
            check_mul_assign(&name, &base, &a, &scalar_one);

            let name = format!("ZeroGroup: 0 * b {}", i);
            check_mul(&name, &affine_zero, &group_zero, &b);
            let name = format!("ZeroGroupAssign: 0 * b {}", i);
            check_mul_assign(&name, &affine_zero, &group_zero, &b);
        }
    }

    #[test]
    fn test_constant_times_constant() {
        run_test(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_constant_times_public() {
        run_test(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_constant_times_private() {
        run_test(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_public_times_constant() {
        run_test(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_public_times_public() {
        run_test(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_public_times_private() {
        run_test(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_private_times_constant() {
        run_test(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_private_times_public() {
        run_test(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_private_times_private() {
        run_test(Mode::Private, Mode::Private);
    }
}
