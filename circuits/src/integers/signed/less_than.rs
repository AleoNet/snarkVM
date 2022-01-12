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

impl<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize> LessThan<Self>
    for Signed<E, I, U, SIZE>
{
    type Boolean = Boolean<E>;
    type Output = Boolean<E>;

    ///
    /// Returns `true` if `self` is less than `other`.
    ///
    /// TODO (@pranav) Number of constraints.
    ///
    fn is_lt(&self, other: &Self) -> Self::Output {
        let mut result = Boolean::new(Mode::Constant, false);
        let mut prev_bits_equal = Boolean::new(Mode::Constant, true);

        let mut reversed_bit_pairs = self.bits_le.iter().zip(other.bits_le.iter()).rev();
        let (self_msb, other_msb) = reversed_bit_pairs.next().expect("Signed must contain at least one bit");

        result = result.or(&prev_bits_equal.and(&self_msb.and(&!other_msb)));
        prev_bits_equal = prev_bits_equal.and(&!self_msb.xor(other_msb));

        for (self_bit, other_bit) in reversed_bit_pairs {
            result = result.or(&prev_bits_equal.and(&(!self_bit).and(other_bit)));
            prev_bits_equal = prev_bits_equal.and(&!(self_bit.xor(other_bit)));
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

    //const ITERATIONS: usize = 100;

    //#[test]
    //fn test_is_eq() {
    //    // Constant == Constant
    //    for i in 0..ITERATIONS {
    //        // Sample two random elements.
    //        let a = Signed::<Circuit, i64, 64>::new(Mode::Constant, UniformRand::rand(&mut thread_rng()));
    //        let b = Signed::<Circuit, i64, 64>::new(Mode::Constant, UniformRand::rand(&mut thread_rng()));

    //        Circuit::scoped(&format!("Constant Less Than {}", i), |scope| {
    //            let equals = a.is_eq(&b);
    //            assert!(!equals.eject_value());

    //            assert_eq!(2, scope.num_constants_in_scope());
    //            assert_eq!(0, scope.num_public_in_scope());
    //            assert_eq!(0, scope.num_private_in_scope());
    //            assert_eq!(0, scope.num_constraints_in_scope());
    //        });

    //        Circuit::scoped(&format!("Constant Not Less Than {}", i), |scope| {
    //            let equals = a.is_neq(&b);
    //            assert!(equals.eject_value());

    //            assert_eq!(2, scope.num_constants_in_scope());
    //            assert_eq!(0, scope.num_public_in_scope());
    //            assert_eq!(0, scope.num_private_in_scope());
    //            assert_eq!(0, scope.num_constraints_in_scope());
    //        });
    //    }

    //    // Constant == Public
    //    for i in 0..ITERATIONS {
    //        // Sample two random elements.
    //        let a = Signed::<Circuit, i64, 64>::new(Mode::Constant, UniformRand::rand(&mut thread_rng()));
    //        let b = Signed::<Circuit, i64, 64>::new(Mode::Public, UniformRand::rand(&mut thread_rng()));

    //        Circuit::scoped(&format!("Constant and Public Less Than {}", i), |scope| {
    //            let equals = a.is_eq(&b);
    //            assert!(!equals.eject_value());

    //            assert_eq!(0, scope.num_constants_in_scope());
    //            assert_eq!(0, scope.num_public_in_scope());
    //            assert_eq!(5, scope.num_private_in_scope());
    //            assert_eq!(8, scope.num_constraints_in_scope());
    //            assert!(scope.is_satisfied());
    //        });

    //        Circuit::scoped(&format!("Constant and Public Not Less Than {}", i), |scope| {
    //            let equals = a.is_neq(&b);
    //            assert!(equals.eject_value());

    //            assert_eq!(0, scope.num_constants_in_scope());
    //            assert_eq!(0, scope.num_public_in_scope());
    //            assert_eq!(5, scope.num_private_in_scope());
    //            assert_eq!(8, scope.num_constraints_in_scope());
    //            assert!(scope.is_satisfied());
    //        });
    //    }

    //    // Public == Constant
    //    for i in 0..ITERATIONS {
    //        // Sample two random elements.
    //        let a = Signed::<Circuit, i64, 64>::new(Mode::Public, UniformRand::rand(&mut thread_rng()));
    //        let b = Signed::<Circuit, i64, 64>::new(Mode::Constant, UniformRand::rand(&mut thread_rng()));

    //        Circuit::scoped(&format!("Public and Constant Less Than {}", i), |scope| {
    //            let equals = a.is_eq(&b);
    //            assert!(!equals.eject_value());

    //            assert_eq!(0, scope.num_constants_in_scope());
    //            assert_eq!(0, scope.num_public_in_scope());
    //            assert_eq!(5, scope.num_private_in_scope());
    //            assert_eq!(8, scope.num_constraints_in_scope());
    //            assert!(scope.is_satisfied());
    //        });

    //        Circuit::scoped(&format!("Public and Constant Not Less Than {}", i), |scope| {
    //            let equals = a.is_neq(&b);
    //            assert!(equals.eject_value());

    //            assert_eq!(0, scope.num_constants_in_scope());
    //            assert_eq!(0, scope.num_public_in_scope());
    //            assert_eq!(5, scope.num_private_in_scope());
    //            assert_eq!(8, scope.num_constraints_in_scope());
    //            assert!(scope.is_satisfied());
    //        });
    //    }

    //    // Public == Public
    //    for i in 0..ITERATIONS {
    //        // Sample two random elements.
    //        let a = Signed::<Circuit, i64, 64>::new(Mode::Public, UniformRand::rand(&mut thread_rng()));
    //        let b = Signed::<Circuit, i64, 64>::new(Mode::Public, UniformRand::rand(&mut thread_rng()));

    //        Circuit::scoped(&format!("Public Less Than {}", i), |scope| {
    //            let equals = a.is_eq(&b);
    //            assert!(!equals.eject_value());

    //            assert_eq!(0, scope.num_constants_in_scope());
    //            assert_eq!(0, scope.num_public_in_scope());
    //            assert_eq!(5, scope.num_private_in_scope());
    //            assert_eq!(8, scope.num_constraints_in_scope());
    //            assert!(scope.is_satisfied());
    //        });

    //        Circuit::scoped(&format!("Public Not Less Than {}", i), |scope| {
    //            let equals = a.is_neq(&b);
    //            assert!(equals.eject_value());

    //            assert_eq!(0, scope.num_constants_in_scope());
    //            assert_eq!(0, scope.num_public_in_scope());
    //            assert_eq!(5, scope.num_private_in_scope());
    //            assert_eq!(8, scope.num_constraints_in_scope());
    //            assert!(scope.is_satisfied());
    //        });
    //    }

    //    // Private == Private
    //    for i in 0..ITERATIONS {
    //        // Sample two random elements.
    //        let a = Signed::<Circuit, i64, 64>::new(Mode::Private, UniformRand::rand(&mut thread_rng()));
    //        let b = Signed::<Circuit, i64, 64>::new(Mode::Private, UniformRand::rand(&mut thread_rng()));

    //        Circuit::scoped(&format!("Private Less Than {}", i), |scope| {
    //            let equals = a.is_eq(&b);
    //            assert!(!equals.eject_value());

    //            assert_eq!(0, scope.num_constants_in_scope());
    //            assert_eq!(0, scope.num_public_in_scope());
    //            assert_eq!(5, scope.num_private_in_scope());
    //            assert_eq!(8, scope.num_constraints_in_scope());
    //            assert!(scope.is_satisfied());
    //        });

    //        Circuit::scoped(&format!("Private Not Less Than {}", i), |scope| {
    //            let equals = a.is_neq(&b);
    //            assert!(equals.eject_value());

    //            assert_eq!(0, scope.num_constants_in_scope());
    //            assert_eq!(0, scope.num_public_in_scope());
    //            assert_eq!(5, scope.num_private_in_scope());
    //            assert_eq!(8, scope.num_constraints_in_scope());
    //            assert!(scope.is_satisfied());
    //        });
    //    }
    //}
}
