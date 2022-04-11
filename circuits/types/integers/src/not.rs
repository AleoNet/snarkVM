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

impl<E: Environment, I: IntegerType> Not for Integer<E, I> {
    type Output = Integer<E, I>;

    fn not(self) -> Self::Output {
        (&self).not()
    }
}

impl<E: Environment, I: IntegerType> Not for &Integer<E, I> {
    type Output = Integer<E, I>;

    fn not(self) -> Self::Output {
        // Flip each bit in the representation of the `self` integer.
        Integer { bits_le: self.bits_le.iter().map(|b| !b).collect(), phantom: Default::default() }
    }
}

impl<E: Environment, I: IntegerType> MetadataForOp<dyn Not<Output = Integer<E, I>>> for Integer<E, I> {
    type Case = Mode;

    fn count(_input: &Self::Case) -> Count {
        Count::exact(0, 0, 0, 0)
    }

    fn output_mode(input: &Self::Case) -> Mode {
        match input {
            Mode::Constant => Mode::Constant,
            _ => Mode::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::{assert_count, assert_output_mode, Circuit};
    use snarkvm_utilities::{test_rng, UniformRand};
    use test_utilities::*;

    const ITERATIONS: usize = 128;

    #[rustfmt::skip]
    fn check_not<I: IntegerType + Not<Output=I>>(
        name: &str,
        first: I,
        mode: Mode,
    ) {
        let a = Integer::<Circuit, I>::new(mode, first);
        let case = format!("(!{})", a.eject_value());
        let expected = !first;

        // TODO: Use `test_utilities` once they use `MetadataForOp`.
        Circuit::scope(name, || {
            let candidate = a.not();
            assert_eq!(expected, candidate.eject_value());
            assert_count!(Integer<Circuit, I>, Not<Output=Integer<Circuit, I>>, &mode);
            assert_output_mode!(candidate, Integer<Circuit, I>, Not<Output=Integer<Circuit, I>>, &mode);
        });
    }

    fn run_test<I: IntegerType + Not<Output = I>>(mode: Mode) {
        for i in 0..ITERATIONS {
            let name = format!("Not: {} {}", mode, i);
            let value: I = UniformRand::rand(&mut test_rng());
            check_not(&name, value, mode);
        }

        // Check the 0 case.
        let name = format!("Not: {} zero", mode);
        check_not(&name, I::zero(), mode);

        // Check the 1 case.
        let name = format!("Not: {} one", mode);
        check_not(&name, I::one(), mode);
    }

    #[test]
    fn test_u8_not() {
        type I = u8;
        run_test::<I>(Mode::Constant);
        run_test::<I>(Mode::Public);
        run_test::<I>(Mode::Private);
    }

    #[test]
    fn test_i8_not() {
        type I = i8;
        run_test::<I>(Mode::Constant);
        run_test::<I>(Mode::Public);
        run_test::<I>(Mode::Private);
    }

    #[test]
    fn test_u16_not() {
        type I = u16;
        run_test::<I>(Mode::Constant);
        run_test::<I>(Mode::Public);
        run_test::<I>(Mode::Private);
    }

    #[test]
    fn test_i16_not() {
        type I = i16;
        run_test::<I>(Mode::Constant);
        run_test::<I>(Mode::Public);
        run_test::<I>(Mode::Private);
    }

    #[test]
    fn test_u32_not() {
        type I = u32;
        run_test::<I>(Mode::Constant);
        run_test::<I>(Mode::Public);
        run_test::<I>(Mode::Private);
    }

    #[test]
    fn test_i32_not() {
        type I = i32;
        run_test::<I>(Mode::Constant);
        run_test::<I>(Mode::Public);
        run_test::<I>(Mode::Private);
    }

    #[test]
    fn test_u64_not() {
        type I = u64;
        run_test::<I>(Mode::Constant);
        run_test::<I>(Mode::Public);
        run_test::<I>(Mode::Private);
    }

    #[test]
    fn test_i64_not() {
        type I = i64;
        run_test::<I>(Mode::Constant);
        run_test::<I>(Mode::Public);
        run_test::<I>(Mode::Private);
    }

    #[test]
    fn test_u128_not() {
        type I = u128;
        run_test::<I>(Mode::Constant);
        run_test::<I>(Mode::Public);
        run_test::<I>(Mode::Private);
    }

    #[test]
    fn test_i128_not() {
        type I = i128;
        run_test::<I>(Mode::Constant);
        run_test::<I>(Mode::Public);
        run_test::<I>(Mode::Private);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_not() {
        type I = u8;
        for value in I::MIN..=I::MAX {
            let name = format!("Not: {}", Mode::Constant);
            check_not(&name, value, Mode::Constant);

            let name = format!("Not: {}", Mode::Public);
            check_not(&name, value, Mode::Public);

            let name = format!("Not: {}", Mode::Private);
            check_not(&name, value, Mode::Private);
        }
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_not() {
        type I = i8;
        for value in I::MIN..=I::MAX {
            let name = format!("Not: {}", Mode::Constant);
            check_not(&name, value, Mode::Constant);

            let name = format!("Not: {}", Mode::Public);
            check_not(&name, value, Mode::Public);

            let name = format!("Not: {}", Mode::Private);
            check_not(&name, value, Mode::Private);
        }
    }
}
