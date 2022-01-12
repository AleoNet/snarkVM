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
use itertools::all;

impl<E: Environment, I: PrimitiveUnsignedInteger, const SIZE: usize> Equal<Self> for Unsigned<E, I, SIZE> {
    type Boolean = Boolean<E>;
    type Output = Boolean<E>;

    ///
    /// Returns `true` if `self` and `other` are equal.
    ///
    /// TODO (@pranav) Number of constraints; Is extra logical and for Boolean::new(Mode::Constant, true) free?
    ///
    fn is_eq(&self, other: &Self) -> Self::Output {
        let mut all_bits_eq = self
            .bits_le
            .iter()
            .zip(other.bits_le.iter())
            .map(|(self_bit, other_bit)| self_bit.is_eq(other_bit));
        all_bits_eq.fold(Boolean::new(Mode::Constant, true), |prev_bits_eq, next_bit_eq| {
            prev_bits_eq.and(&next_bit_eq)
        })
    }

    ///
    /// Returns `true` if `self` and `other` are *not* equal.
    ///
    /// This method constructs a boolean that indicates if
    /// `self` and `other ` are *not* equal to each other.
    ///
    /// This method costs 8 constraints.
    ///
    fn is_neq(&self, other: &Self) -> Self::Output {
        !self.is_eq(other)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

    const ITERATIONS: usize = 100;

    #[test]
    fn test_is_eq() {
        // Constant == Constant
        for i in 0..ITERATIONS {
            // Sample two random elements.
            let a = Unsigned::<Circuit, u64, 64>::new(Mode::Constant, UniformRand::rand(&mut thread_rng()));
            let b = Unsigned::<Circuit, u64, 64>::new(Mode::Constant, UniformRand::rand(&mut thread_rng()));

            Circuit::scoped(&format!("Constant Equals {}", i), |scope| {
                let equals = a.is_eq(&b);
                assert!(!equals.eject_value());

                assert_eq!(1, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(0, scope.num_private_in_scope());
                assert_eq!(0, scope.num_constraints_in_scope());
            });

            Circuit::scoped(&format!("Constant Not Equals {}", i), |scope| {
                let equals = a.is_neq(&b);
                assert!(equals.eject_value());

                assert_eq!(1, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(0, scope.num_private_in_scope());
                assert_eq!(0, scope.num_constraints_in_scope());
            });
        }

        // Constant == Public
        for i in 0..ITERATIONS {
            // Sample two random elements.
            let a = Unsigned::<Circuit, u64, 64>::new(Mode::Constant, UniformRand::rand(&mut thread_rng()));
            let b = Unsigned::<Circuit, u64, 64>::new(Mode::Public, UniformRand::rand(&mut thread_rng()));

            Circuit::scoped(&format!("Constant and Public Equals {}", i), |scope| {
                let equals = a.is_eq(&b);
                assert!(!equals.eject_value());

                assert_eq!(1, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(63, scope.num_private_in_scope());
                assert_eq!(126, scope.num_constraints_in_scope());
                assert!(scope.is_satisfied());
            });

            Circuit::scoped(&format!("Constant and Public Not Equals {}", i), |scope| {
                let equals = a.is_neq(&b);
                assert!(equals.eject_value());

                assert_eq!(1, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(63, scope.num_private_in_scope());
                assert_eq!(126, scope.num_constraints_in_scope());
                assert!(scope.is_satisfied());
            });
        }

        // Public == Constant
        for i in 0..ITERATIONS {
            // Sample two random elements.
            let a = Unsigned::<Circuit, u64, 64>::new(Mode::Public, UniformRand::rand(&mut thread_rng()));
            let b = Unsigned::<Circuit, u64, 64>::new(Mode::Constant, UniformRand::rand(&mut thread_rng()));

            Circuit::scoped(&format!("Public and Constant Equals {}", i), |scope| {
                let equals = a.is_eq(&b);
                assert!(!equals.eject_value());

                assert_eq!(1, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(63, scope.num_private_in_scope());
                assert_eq!(126, scope.num_constraints_in_scope());
                assert!(scope.is_satisfied());
            });

            Circuit::scoped(&format!("Public and Constant Not Equals {}", i), |scope| {
                let equals = a.is_neq(&b);
                assert!(equals.eject_value());

                assert_eq!(1, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(63, scope.num_private_in_scope());
                assert_eq!(126, scope.num_constraints_in_scope());
                assert!(scope.is_satisfied());
            });
        }

        // Public == Public
        for i in 0..ITERATIONS {
            // Sample two random elements.
            let a = Unsigned::<Circuit, u64, 64>::new(Mode::Public, UniformRand::rand(&mut thread_rng()));
            let b = Unsigned::<Circuit, u64, 64>::new(Mode::Public, UniformRand::rand(&mut thread_rng()));

            Circuit::scoped(&format!("Public Equals {}", i), |scope| {
                let equals = a.is_eq(&b);
                assert!(!equals.eject_value());

                assert_eq!(1, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(127, scope.num_private_in_scope());
                assert_eq!(254, scope.num_constraints_in_scope());
                assert!(scope.is_satisfied());
            });

            Circuit::scoped(&format!("Public Not Equals {}", i), |scope| {
                let equals = a.is_neq(&b);
                assert!(equals.eject_value());

                assert_eq!(1, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(127, scope.num_private_in_scope());
                assert_eq!(254, scope.num_constraints_in_scope());
                assert!(scope.is_satisfied());
            });
        }

        // Private == Private
        for i in 0..ITERATIONS {
            // Sample two random elements.
            let a = Unsigned::<Circuit, u64, 64>::new(Mode::Private, UniformRand::rand(&mut thread_rng()));
            let b = Unsigned::<Circuit, u64, 64>::new(Mode::Private, UniformRand::rand(&mut thread_rng()));

            Circuit::scoped(&format!("Private Equals {}", i), |scope| {
                let equals = a.is_eq(&b);
                assert!(!equals.eject_value());

                assert_eq!(1, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(127, scope.num_private_in_scope());
                assert_eq!(254, scope.num_constraints_in_scope());
                assert!(scope.is_satisfied());
            });

            Circuit::scoped(&format!("Private Not Equals {}", i), |scope| {
                let equals = a.is_neq(&b);
                assert!(equals.eject_value());

                assert_eq!(1, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(127, scope.num_private_in_scope());
                assert_eq!(254, scope.num_constraints_in_scope());
                assert!(scope.is_satisfied());
            });
        }
    }
}
