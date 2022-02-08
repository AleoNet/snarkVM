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

impl<E: Environment, I: IntegerType> Not for Integer<E, I> {
    type Output = Integer<E, I>;

    fn not(self) -> Self::Output {
        // Flip all bits.
        Integer { bits_le: self.bits_le.iter().map(|b| !b).collect(), phantom: Default::default() }
    }
}

impl<E: Environment, I: IntegerType> Not for &Integer<E, I> {
    type Output = Integer<E, I>;

    fn not(self) -> Self::Output {
        !(self.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;
    use test_utilities::*;

    use rand::thread_rng;

    const ITERATIONS: usize = 128;

    #[rustfmt::skip]
    fn run_test<I: IntegerType + Not<Output = I>>(
        mode: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        let check_not = | name: &str, first: I | {
            let a = Integer::<Circuit, I>::new(mode, first);
            let case = format!("(!{})", a.eject_value());
            let expected = !first;
            check_unary_operation_passes(name, &case, expected, &a, |a: &Integer<Circuit, I> | { a.not() }, num_constants, num_public, num_private, num_constraints);
        };

        for i in 0..ITERATIONS {
            let value: I = UniformRand::rand(&mut thread_rng());

            let name = format!("Not: {} {}", mode, i);
            check_not(&name, value)
        }

        // Check the 0 case.
        let name = format!("Not: {} zero", mode);
        check_not(&name, I::zero());

        // Check the 1 case.
        let name = format!("Not: {} one", mode);
        check_not(&name, I::one());
    }

    #[test]
    fn test_u8_not() {
        type I = u8;
        run_test::<I>(Mode::Constant, 0, 0, 0, 0);
        run_test::<I>(Mode::Public, 0, 0, 0, 0);
        run_test::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_not() {
        type I = i8;
        run_test::<I>(Mode::Constant, 0, 0, 0, 0);
        run_test::<I>(Mode::Public, 0, 0, 0, 0);
        run_test::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_not() {
        type I = u16;
        run_test::<I>(Mode::Constant, 0, 0, 0, 0);
        run_test::<I>(Mode::Public, 0, 0, 0, 0);
        run_test::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_not() {
        type I = i16;
        run_test::<I>(Mode::Constant, 0, 0, 0, 0);
        run_test::<I>(Mode::Public, 0, 0, 0, 0);
        run_test::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_not() {
        type I = u32;
        run_test::<I>(Mode::Constant, 0, 0, 0, 0);
        run_test::<I>(Mode::Public, 0, 0, 0, 0);
        run_test::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_not() {
        type I = i32;
        run_test::<I>(Mode::Constant, 0, 0, 0, 0);
        run_test::<I>(Mode::Public, 0, 0, 0, 0);
        run_test::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_not() {
        type I = u64;
        run_test::<I>(Mode::Constant, 0, 0, 0, 0);
        run_test::<I>(Mode::Public, 0, 0, 0, 0);
        run_test::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_not() {
        type I = i64;
        run_test::<I>(Mode::Constant, 0, 0, 0, 0);
        run_test::<I>(Mode::Public, 0, 0, 0, 0);
        run_test::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_not() {
        type I = u128;
        run_test::<I>(Mode::Constant, 0, 0, 0, 0);
        run_test::<I>(Mode::Public, 0, 0, 0, 0);
        run_test::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_not() {
        type I = i128;
        run_test::<I>(Mode::Constant, 0, 0, 0, 0);
        run_test::<I>(Mode::Public, 0, 0, 0, 0);
        run_test::<I>(Mode::Private, 0, 0, 0, 0);
    }
}
