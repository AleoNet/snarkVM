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

impl<E: Environment, I: IntegerType> One for Integer<E, I> {
    type Boolean = Boolean<E>;

    fn one() -> Self {
        Integer::new(Mode::Constant, I::one())
    }

    fn is_one(&self) -> Self::Boolean {
        self.is_equal(&Integer::one())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{assert_circuit, Circuit};

    fn check_one<I: IntegerType>() {
        Circuit::scoped("One", || {
            assert_circuit!(0, 0, 0, 0);
            assert_eq!(I::one(), Integer::<Circuit, I>::one().eject_value());
            assert_circuit!(I::BITS, 0, 0, 0);
        });
        // Should equal 1.
        assert!(Integer::<Circuit, I>::one().is_one().eject_value());
        // Should not equal 0.
        assert!(!Integer::<Circuit, I>::one().is_zero().eject_value());
    }

    #[test]
    fn test_u8_one() {
        check_one::<u8>();
    }

    #[test]
    fn test_i8_one() {
        check_one::<i8>();
    }

    #[test]
    fn test_u16_one() {
        check_one::<u16>();
    }

    #[test]
    fn test_i16_one() {
        check_one::<i16>();
    }

    #[test]
    fn test_u32_one() {
        check_one::<u32>();
    }

    #[test]
    fn test_i32_one() {
        check_one::<i32>();
    }

    #[test]
    fn test_u64_one() {
        check_one::<u64>();
    }

    #[test]
    fn test_i64_one() {
        check_one::<i64>();
    }

    #[test]
    fn test_u128_one() {
        check_one::<u128>();
    }

    #[test]
    fn test_i128_one() {
        check_one::<i128>();
    }
}
