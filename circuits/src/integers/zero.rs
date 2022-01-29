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

impl<E: Environment, I: IntegerType> Zero for Integer<E, I> {
    type Boolean = Boolean<E>;

    fn zero() -> Self {
        Integer::new(Mode::Constant, I::zero())
    }

    fn is_zero(&self) -> Self::Boolean {
        self.is_eq(&Integer::zero())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;

    fn check_zero<I: IntegerType>() {
        Circuit::scoped("Zero", || {
            assert_eq!(0, Circuit::num_constants_in_scope());
            assert_eq!(0, Circuit::num_public_in_scope());
            assert_eq!(0, Circuit::num_private_in_scope());
            assert_eq!(0, Circuit::num_constraints_in_scope());

            assert_eq!(I::zero(), Integer::<Circuit, I>::zero().eject_value());

            assert_eq!(I::BITS, Circuit::num_constants_in_scope(), "(num_constants)");
            assert_eq!(0, Circuit::num_public_in_scope(), "(num_public)");
            assert_eq!(0, Circuit::num_private_in_scope(), "(num_private)");
            assert_eq!(0, Circuit::num_constraints_in_scope(), "(num_constraints)");

            assert!(Circuit::is_satisfied(), "(is_satisfied)");
        });

        let candidate = Integer::<Circuit, I>::zero();
        // Should equal 0.
        assert!(candidate.is_zero().eject_value());
        // Should not equal 1.
        assert!(!candidate.is_one().eject_value());
    }

    #[test]
    fn test_u8_zero() {
        check_zero::<u8>();
    }

    #[test]
    fn test_i8_zero() {
        check_zero::<i8>();
    }

    #[test]
    fn test_u16_zero() {
        check_zero::<u16>();
    }

    #[test]
    fn test_i16_zero() {
        check_zero::<i16>();
    }

    #[test]
    fn test_u32_zero() {
        check_zero::<u32>();
    }

    #[test]
    fn test_i32_zero() {
        check_zero::<i32>();
    }

    #[test]
    fn test_u64_zero() {
        check_zero::<u64>();
    }

    #[test]
    fn test_i64_zero() {
        check_zero::<i64>();
    }

    #[test]
    fn test_u128_zero() {
        check_zero::<u128>();
    }

    #[test]
    fn test_i128_zero() {
        check_zero::<i128>();
    }
}
