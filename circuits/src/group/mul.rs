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

impl<E: Environment> Mul<Field<E>> for Affine<E> {
    type Output = Self;

    fn mul(self, other: Field<E>) -> Self::Output {
        self * &other
    }
}

impl<E: Environment> Mul<Field<E>> for &Affine<E> {
    type Output = Self;

    fn mul(self, other: Field<E>) -> Self::Output {
        let mut output = self;
        output *= other;
        output
    }
}

impl<E: Environment> Mul<&Field<E>> for Affine<E> {
    type Output = Self;

    fn mul(self, other: &Field<E>) -> Self::Output {
        let mut output = self;
        output *= other;
        output
    }
}

impl<E: Environment> Mul<&Field<E>> for &Affine<E> {
    type Output = Affine<E>;

    fn mul(self, other: &Field<E>) -> Self::Output {
        let mut output = (*self).clone();
        output *= other;
        output
    }
}

impl<E: Environment> Mul<Affine<E>> for Field<E> {
    type Output = Affine<E>;

    fn mul(self, other: Affine<E>) -> Self::Output {
        other * &self
    }
}

impl<E: Environment> Mul<Affine<E>> for &Field<E> {
    type Output = Affine<E>;

    fn mul(self, other: Affine<E>) -> Self::Output {
        &other * self
    }
}

impl<E: Environment> Mul<&Affine<E>> for Field<E> {
    type Output = Affine<E>;

    fn mul(self, other: &Affine<E>) -> Self::Output {
        other * &self
    }
}

impl<E: Environment> Mul<&Affine<E>> for &Field<E> {
    type Output = Affine<E>;

    fn mul(self, other: &Affine<E>) -> Self::Output {
        other * self
    }
}

impl<E: Environment> MulAssign<Field<E>> for Affine<E> {
    fn mul_assign(&mut self, other: Field<E>) {
        *self *= &other;
    }
}

impl<E: Environment> MulAssign<Field<E>> for &Affine<E> {
    fn mul_assign(&mut self, other: Field<E>) {
        *self *= &other;
    }
}

impl<E: Environment> MulAssign<&Field<E>> for Affine<E> {
    fn mul_assign(&mut self, other: &Field<E>) {
        *self *= other;
    }
}

impl<E: Environment> MulAssign<&Field<E>> for &Affine<E> {
    fn mul_assign(&mut self, other: &Field<E>) {
        // let mut output = Affine::zero();
        //
        // for (i, bit) in other.to_bits_be().iter().enumerate() {
        //     output = output.double();
        //     if bit {
        //         output += self;
        //     }
        // }

        // let mut output = Affine::zero();
        unimplemented!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;

    const ITERATIONS: usize = 1_000;

    #[test]
    fn test_mul() {
        // let one = <Circuit as Environment>::BaseField::one();
        // let two = one + one;

        // // Constant * Constant
        // Circuit::scoped("Constant * Constant", |scope| {
        //     let mut expected_product = one;
        //     let mut candidate_product = Field::<Circuit>::one();
        //
        //     for i in 0..ITERATIONS {
        //         expected_product = expected_product * &two;
        //         candidate_product = candidate_product * Field::new(Mode::Constant, two);
        //
        //         assert_eq!((i + 1) * 2, scope.num_constants_in_scope());
        //         assert_eq!(0, scope.num_public_in_scope());
        //         assert_eq!(0, scope.num_private_in_scope());
        //         assert_eq!(0, scope.num_constraints_in_scope());
        //     }
        //
        //     assert_eq!(expected_product, candidate_product.to_value());
        // });
        //
        // // Public * Public
        // Circuit::scoped("Public * Public", |scope| {
        //     let mut expected_product = one;
        //     let mut candidate_product = Field::<Circuit>::new(Mode::Public, one);
        //
        //     for i in 0..ITERATIONS {
        //         expected_product = expected_product * &two;
        //         candidate_product = candidate_product * Field::new(Mode::Public, two);
        //
        //         assert_eq!(0, scope.num_constants_in_scope());
        //         assert_eq!(i + 2, scope.num_public_in_scope());
        //         assert_eq!(i + 1, scope.num_private_in_scope());
        //         assert_eq!(i + 1, scope.num_constraints_in_scope());
        //         assert!(scope.is_satisfied());
        //     }
        //
        //     assert_eq!(expected_product, candidate_product.to_value());
        // });
        //
        // // Private * Private
        // Circuit::scoped("Private * Private", |scope| {
        //     let mut expected_product = one;
        //     let mut candidate_product = Field::<Circuit>::new(Mode::Private, one);
        //
        //     for i in 0..ITERATIONS {
        //         expected_product = expected_product * &two;
        //         candidate_product = candidate_product * Field::new(Mode::Private, two);
        //
        //         assert_eq!(0, scope.num_constants_in_scope());
        //         assert_eq!(0, scope.num_public_in_scope());
        //         assert_eq!(i * 2 + 3, scope.num_private_in_scope());
        //         assert_eq!(i + 1, scope.num_constraints_in_scope());
        //         assert!(scope.is_satisfied());
        //     }
        //
        //     assert_eq!(expected_product, candidate_product.to_value());
        // });
    }
}
