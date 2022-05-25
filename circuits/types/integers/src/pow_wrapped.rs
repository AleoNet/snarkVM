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

impl<E: Environment, I: IntegerType, M: Magnitude> PowWrapped<Integer<E, M>> for Integer<E, I> {
    type Output = Self;

    #[inline]
    fn pow_wrapped(&self, other: &Integer<E, M>) -> Self::Output {
        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the result and return the new constant.
            // This cast is safe since Magnitude other can only be `u8`, `u16`, or `u32`.
            witness!(|self, other| self.wrapping_pow(&other.to_u32().unwrap()))
        } else {
            let mut result = Self::one();
            for bit in other.bits_le.iter().rev() {
                result = (&result).mul_wrapped(&result);
                result = Self::ternary(bit, &result.mul_wrapped(self), &result);
            }
            result
        }
    }
}

impl<E: Environment, I: IntegerType, M: Magnitude> Metrics<dyn PowWrapped<Integer<E, M>, Output = Integer<E, I>>>
    for Integer<E, I>
{
    type Case = (Mode, Mode);

    fn count(case: &Self::Case) -> Count {
        match (case.0, case.1) {
            (Mode::Constant, Mode::Constant) => Count::is(I::BITS, 0, 0, 0),
            (Mode::Constant, _) | (_, Mode::Constant) => {
                let mul_count = count!(Integer<E, I>, MulWrapped<Integer<E, I>, Output=Integer<E, I>>, case);
                (2 * M::BITS * mul_count) + Count::is(2 * I::BITS, 0, I::BITS, I::BITS)
            }
            (_, _) => {
                let mul_count = count!(Integer<E, I>, MulWrapped<Integer<E, I>, Output=Integer<E, I>>, case);
                (2 * M::BITS * mul_count) + Count::is(2 * I::BITS, 0, I::BITS, I::BITS)
            }
        }
    }
}

impl<E: Environment, I: IntegerType, M: Magnitude> OutputMode<dyn PowWrapped<Integer<E, M>, Output = Integer<E, I>>>
    for Integer<E, I>
{
    type Case = (Mode, CircuitType<Integer<E, M>>);

    fn output_mode(case: &Self::Case) -> Mode {
        match (case.0, (case.1.mode(), &case.1)) {
            (Mode::Constant, (Mode::Constant, _)) => Mode::Constant,
            (Mode::Constant, (mode, _)) => match mode {
                Mode::Constant => Mode::Constant,
                _ => Mode::Private,
            },
            (_, (Mode::Constant, case)) => match case {
                // Determine if the constant is all zeros.
                CircuitType::Constant(constant) => match constant.eject_value().is_zero() {
                    true => Mode::Constant,
                    false => Mode::Private,
                },
                _ => E::halt("The constant is required for the output mode of `pow_wrapped` with a constant."),
            },
            (_, _) => Mode::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::{count_is, Circuit, UpdatableCount};
    use snarkvm_utilities::{test_rng, UniformRand};

    use core::{ops::RangeInclusive, panic::RefUnwindSafe};

    // Lowered to 4; we run (~6 * ITERATIONS) cases for most tests.
    const ITERATIONS: u64 = 4;

    fn check_pow<I: IntegerType + RefUnwindSafe, M: Magnitude + RefUnwindSafe>(
        name: &str,
        first: I,
        second: M,
        mode_a: Mode,
        mode_b: Mode,
        count: UpdatableCount,
    ) {
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, M>::new(mode_b, second);
        let expected = first.wrapping_pow(&second.to_u32().unwrap());
        Circuit::scope(name, || {
            let candidate = a.pow_wrapped(&b);
            assert_eq!(expected, candidate.eject_value());
            count.assert_matches(
                Circuit::num_constants_in_scope(),
                Circuit::num_public_in_scope(),
                Circuit::num_private_in_scope(),
                Circuit::num_constraints_in_scope(),
            );
            // assert_output_mode!(PowWrapped(Integer<I>, Integer<M>) => Integer<I>, &(mode_a, CircuitType::from(&b)), candidate);
        });
        Circuit::reset();
    }

    fn run_test<I: IntegerType + RefUnwindSafe, M: Magnitude + RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
        count: UpdatableCount,
    ) {
        for i in 0..ITERATIONS {
            let first: I = UniformRand::rand(&mut test_rng());
            let second: M = UniformRand::rand(&mut test_rng());

            let name = format!("Pow: {} ** {} {}", mode_a, mode_b, i);
            check_pow(&name, first, second, mode_a, mode_b, count);

            let name = format!("Pow Zero: {} ** {} {}", mode_a, mode_b, i);
            check_pow(&name, first, M::zero(), mode_a, mode_b, count);

            let name = format!("Pow One: {} ** {} {}", mode_a, mode_b, i);
            check_pow(&name, first, M::one(), mode_a, mode_b, count);

            // Check that the square is computed correctly.
            let name = format!("Square: {} ** {} {}", mode_a, mode_b, i);
            check_pow(&name, first, M::one() + M::one(), mode_a, mode_b, count);

            // Check that the cube is computed correctly.
            let name = format!("Cube: {} ** {} {}", mode_a, mode_b, i);
            check_pow(&name, first, M::one() + M::one() + M::one(), mode_a, mode_b, count);
        }

        // Test corner cases for exponentiation.
        check_pow("MAX ** MAX", I::MAX, M::MAX, mode_a, mode_b, count);
        check_pow("MIN ** 0", I::MIN, M::zero(), mode_a, mode_b, count);
        check_pow("MAX ** 0", I::MAX, M::zero(), mode_a, mode_b, count);
        check_pow("MIN ** 1", I::MIN, M::one(), mode_a, mode_b, count);
        check_pow("MAX ** 1", I::MAX, M::one(), mode_a, mode_b, count);
    }

    fn run_exhaustive_test<I: IntegerType + RefUnwindSafe, M: Magnitude + RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
        count: UpdatableCount,
    ) where
        RangeInclusive<I>: Iterator<Item = I>,
        RangeInclusive<M>: Iterator<Item = M>,
    {
        for first in I::MIN..=I::MAX {
            for second in M::MIN..=M::MAX {
                let name = format!("Pow: ({} ** {})", first, second);
                check_pow(&name, first, second, mode_a, mode_b, count);
            }
        }
    }

    // Tests for u8 ^ u8.

    #[test]
    fn test_u8_constant_pow_u8_constant() {
        run_test::<u8, u8>(Mode::Constant, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u8_constant_pow_u8_public() {
        run_test::<u8, u8>(Mode::Constant, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u8_constant_pow_u8_private() {
        run_test::<u8, u8>(Mode::Constant, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u8_public_pow_u8_constant() {
        run_test::<u8, u8>(Mode::Public, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u8_public_pow_u8_public() {
        run_test::<u8, u8>(Mode::Public, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u8_public_pow_u8_private() {
        run_test::<u8, u8>(Mode::Public, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u8_private_pow_u8_constant() {
        run_test::<u8, u8>(Mode::Private, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u8_private_pow_u8_public() {
        run_test::<u8, u8>(Mode::Private, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u8_private_pow_u8_private() {
        run_test::<u8, u8>(Mode::Private, Mode::Private, count_is!(0, 0, 0, 0));
    }

    // Tests for u8 ^ u16.

    #[test]
    fn test_u8_constant_pow_u16_constant() {
        run_test::<u8, u16>(Mode::Constant, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u8_constant_pow_u16_public() {
        run_test::<u8, u16>(Mode::Constant, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u8_constant_pow_u16_private() {
        run_test::<u8, u16>(Mode::Constant, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u8_public_pow_u16_constant() {
        run_test::<u8, u16>(Mode::Public, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u8_public_pow_u16_public() {
        run_test::<u8, u16>(Mode::Public, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u8_public_pow_u16_private() {
        run_test::<u8, u16>(Mode::Public, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u8_private_pow_u16_constant() {
        run_test::<u8, u16>(Mode::Private, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u8_private_pow_u16_public() {
        run_test::<u8, u16>(Mode::Private, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u8_private_pow_u16_private() {
        run_test::<u8, u16>(Mode::Private, Mode::Private, count_is!(0, 0, 0, 0));
    }

    // Tests for u8 ^ u32.

    #[test]
    fn test_u8_constant_pow_u32_constant() {
        run_test::<u8, u32>(Mode::Constant, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u8_constant_pow_u32_public() {
        run_test::<u8, u32>(Mode::Constant, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u8_constant_pow_u32_private() {
        run_test::<u8, u32>(Mode::Constant, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u8_public_pow_u32_constant() {
        run_test::<u8, u32>(Mode::Public, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u8_public_pow_u32_public() {
        run_test::<u8, u32>(Mode::Public, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u8_public_pow_u32_private() {
        run_test::<u8, u32>(Mode::Public, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u8_private_pow_u32_constant() {
        run_test::<u8, u32>(Mode::Private, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u8_private_pow_u32_public() {
        run_test::<u8, u32>(Mode::Private, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u8_private_pow_u32_private() {
        run_test::<u8, u32>(Mode::Private, Mode::Private, count_is!(0, 0, 0, 0));
    }

    // Tests for i8 ^ u8.

    #[test]
    fn test_i8_constant_pow_u8_constant() {
        run_test::<i8, u8>(Mode::Constant, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i8_constant_pow_u8_public() {
        run_test::<i8, u8>(Mode::Constant, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i8_constant_pow_u8_private() {
        run_test::<i8, u8>(Mode::Constant, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i8_public_pow_u8_constant() {
        run_test::<i8, u8>(Mode::Public, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i8_public_pow_u8_public() {
        run_test::<i8, u8>(Mode::Public, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i8_public_pow_u8_private() {
        run_test::<i8, u8>(Mode::Public, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i8_private_pow_u8_constant() {
        run_test::<i8, u8>(Mode::Private, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i8_private_pow_u8_public() {
        run_test::<i8, u8>(Mode::Private, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i8_private_pow_u8_private() {
        run_test::<i8, u8>(Mode::Private, Mode::Private, count_is!(0, 0, 0, 0));
    }

    // Tests for i8 ^ u16.

    #[test]
    fn test_i8_constant_pow_u16_constant() {
        run_test::<i8, u16>(Mode::Constant, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i8_constant_pow_u16_public() {
        run_test::<i8, u16>(Mode::Constant, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i8_constant_pow_u16_private() {
        run_test::<i8, u16>(Mode::Constant, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i8_public_pow_u16_constant() {
        run_test::<i8, u16>(Mode::Public, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i8_public_pow_u16_public() {
        run_test::<i8, u16>(Mode::Public, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i8_public_pow_u16_private() {
        run_test::<i8, u16>(Mode::Public, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i8_private_pow_u16_constant() {
        run_test::<i8, u16>(Mode::Private, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i8_private_pow_u16_public() {
        run_test::<i8, u16>(Mode::Private, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i8_private_pow_u16_private() {
        run_test::<i8, u16>(Mode::Private, Mode::Private, count_is!(0, 0, 0, 0));
    }

    // Tests for i8 ^ u32.

    #[test]
    fn test_i8_constant_pow_u32_constant() {
        run_test::<i8, u32>(Mode::Constant, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i8_constant_pow_u32_public() {
        run_test::<i8, u32>(Mode::Constant, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i8_constant_pow_u32_private() {
        run_test::<i8, u32>(Mode::Constant, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i8_public_pow_u32_constant() {
        run_test::<i8, u32>(Mode::Public, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i8_public_pow_u32_public() {
        run_test::<i8, u32>(Mode::Public, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i8_public_pow_u32_private() {
        run_test::<i8, u32>(Mode::Public, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i8_private_pow_u32_constant() {
        run_test::<i8, u32>(Mode::Private, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i8_private_pow_u32_public() {
        run_test::<i8, u32>(Mode::Private, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i8_private_pow_u32_private() {
        run_test::<i8, u32>(Mode::Private, Mode::Private, count_is!(0, 0, 0, 0));
    }

    // Tests for u16 ^ u8.

    #[test]
    fn test_u16_constant_pow_u8_constant() {
        run_test::<u16, u8>(Mode::Constant, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u16_constant_pow_u8_public() {
        run_test::<u16, u8>(Mode::Constant, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u16_constant_pow_u8_private() {
        run_test::<u16, u8>(Mode::Constant, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u16_public_pow_u8_constant() {
        run_test::<u16, u8>(Mode::Public, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u16_public_pow_u8_public() {
        run_test::<u16, u8>(Mode::Public, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u16_public_pow_u8_private() {
        run_test::<u16, u8>(Mode::Public, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u16_private_pow_u8_constant() {
        run_test::<u16, u8>(Mode::Private, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u16_private_pow_u8_public() {
        run_test::<u16, u8>(Mode::Private, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u16_private_pow_u8_private() {
        run_test::<u16, u8>(Mode::Private, Mode::Private, count_is!(0, 0, 0, 0));
    }

    // Tests for u16 ^ u16.

    #[test]
    fn test_u16_constant_pow_u16_constant() {
        run_test::<u16, u16>(Mode::Constant, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u16_constant_pow_u16_public() {
        run_test::<u16, u16>(Mode::Constant, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u16_constant_pow_u16_private() {
        run_test::<u16, u16>(Mode::Constant, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u16_public_pow_u16_constant() {
        run_test::<u16, u16>(Mode::Public, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u16_public_pow_u16_public() {
        run_test::<u16, u16>(Mode::Public, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u16_public_pow_u16_private() {
        run_test::<u16, u16>(Mode::Public, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u16_private_pow_u16_constant() {
        run_test::<u16, u16>(Mode::Private, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u16_private_pow_u16_public() {
        run_test::<u16, u16>(Mode::Private, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u16_private_pow_u16_private() {
        run_test::<u16, u16>(Mode::Private, Mode::Private, count_is!(0, 0, 0, 0));
    }

    // Tests for u16 ^ u32.

    #[test]
    fn test_u16_constant_pow_u32_constant() {
        run_test::<u16, u32>(Mode::Constant, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u16_constant_pow_u32_public() {
        run_test::<u16, u32>(Mode::Constant, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u16_constant_pow_u32_private() {
        run_test::<u16, u32>(Mode::Constant, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u16_public_pow_u32_constant() {
        run_test::<u16, u32>(Mode::Public, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u16_public_pow_u32_public() {
        run_test::<u16, u32>(Mode::Public, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u16_public_pow_u32_private() {
        run_test::<u16, u32>(Mode::Public, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u16_private_pow_u32_constant() {
        run_test::<u16, u32>(Mode::Private, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u16_private_pow_u32_public() {
        run_test::<u16, u32>(Mode::Private, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u16_private_pow_u32_private() {
        run_test::<u16, u32>(Mode::Private, Mode::Private, count_is!(0, 0, 0, 0));
    }

    // Tests for i16 ^ u8.

    #[test]
    fn test_i16_constant_pow_u8_constant() {
        run_test::<i16, u8>(Mode::Constant, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i16_constant_pow_u8_public() {
        run_test::<i16, u8>(Mode::Constant, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i16_constant_pow_u8_private() {
        run_test::<i16, u8>(Mode::Constant, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i16_public_pow_u8_constant() {
        run_test::<i16, u8>(Mode::Public, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i16_public_pow_u8_public() {
        run_test::<i16, u8>(Mode::Public, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i16_public_pow_u8_private() {
        run_test::<i16, u8>(Mode::Public, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i16_private_pow_u8_constant() {
        run_test::<i16, u8>(Mode::Private, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i16_private_pow_u8_public() {
        run_test::<i16, u8>(Mode::Private, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i16_private_pow_u8_private() {
        run_test::<i16, u8>(Mode::Private, Mode::Private, count_is!(0, 0, 0, 0));
    }

    // Tests for i16 ^ u16.

    #[test]
    fn test_i16_constant_pow_u16_constant() {
        run_test::<i16, u16>(Mode::Constant, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i16_constant_pow_u16_public() {
        run_test::<i16, u16>(Mode::Constant, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i16_constant_pow_u16_private() {
        run_test::<i16, u16>(Mode::Constant, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i16_public_pow_u16_constant() {
        run_test::<i16, u16>(Mode::Public, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i16_public_pow_u16_public() {
        run_test::<i16, u16>(Mode::Public, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i16_public_pow_u16_private() {
        run_test::<i16, u16>(Mode::Public, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i16_private_pow_u16_constant() {
        run_test::<i16, u16>(Mode::Private, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i16_private_pow_u16_public() {
        run_test::<i16, u16>(Mode::Private, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i16_private_pow_u16_private() {
        run_test::<i16, u16>(Mode::Private, Mode::Private, count_is!(0, 0, 0, 0));
    }

    // Tests for i16 ^ u32.

    #[test]
    fn test_i16_constant_pow_u32_constant() {
        run_test::<i16, u32>(Mode::Constant, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i16_constant_pow_u32_public() {
        run_test::<i16, u32>(Mode::Constant, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i16_constant_pow_u32_private() {
        run_test::<i16, u32>(Mode::Constant, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i16_public_pow_u32_constant() {
        run_test::<i16, u32>(Mode::Public, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i16_public_pow_u32_public() {
        run_test::<i16, u32>(Mode::Public, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i16_public_pow_u32_private() {
        run_test::<i16, u32>(Mode::Public, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i16_private_pow_u32_constant() {
        run_test::<i16, u32>(Mode::Private, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i16_private_pow_u32_public() {
        run_test::<i16, u32>(Mode::Private, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i16_private_pow_u32_private() {
        run_test::<i16, u32>(Mode::Private, Mode::Private, count_is!(0, 0, 0, 0));
    }

    // Tests for u32 ^ u8.

    #[test]
    fn test_u32_constant_pow_u8_constant() {
        run_test::<u32, u8>(Mode::Constant, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u32_constant_pow_u8_public() {
        run_test::<u32, u8>(Mode::Constant, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u32_constant_pow_u8_private() {
        run_test::<u32, u8>(Mode::Constant, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u32_public_pow_u8_constant() {
        run_test::<u32, u8>(Mode::Public, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u32_public_pow_u8_public() {
        run_test::<u32, u8>(Mode::Public, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u32_public_pow_u8_private() {
        run_test::<u32, u8>(Mode::Public, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u32_private_pow_u8_constant() {
        run_test::<u32, u8>(Mode::Private, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u32_private_pow_u8_public() {
        run_test::<u32, u8>(Mode::Private, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u32_private_pow_u8_private() {
        run_test::<u32, u8>(Mode::Private, Mode::Private, count_is!(0, 0, 0, 0));
    }

    // Tests for u32 ^ u16.

    #[test]
    fn test_u32_constant_pow_u16_constant() {
        run_test::<u32, u16>(Mode::Constant, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u32_constant_pow_u16_public() {
        run_test::<u32, u16>(Mode::Constant, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u32_constant_pow_u16_private() {
        run_test::<u32, u16>(Mode::Constant, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u32_public_pow_u16_constant() {
        run_test::<u32, u16>(Mode::Public, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u32_public_pow_u16_public() {
        run_test::<u32, u16>(Mode::Public, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u32_public_pow_u16_private() {
        run_test::<u32, u16>(Mode::Public, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u32_private_pow_u16_constant() {
        run_test::<u32, u16>(Mode::Private, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u32_private_pow_u16_public() {
        run_test::<u32, u16>(Mode::Private, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u32_private_pow_u16_private() {
        run_test::<u32, u16>(Mode::Private, Mode::Private, count_is!(0, 0, 0, 0));
    }

    // Tests for u32 ^ u32.

    #[test]
    fn test_u32_constant_pow_u32_constant() {
        run_test::<u32, u32>(Mode::Constant, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u32_constant_pow_u32_public() {
        run_test::<u32, u32>(Mode::Constant, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u32_constant_pow_u32_private() {
        run_test::<u32, u32>(Mode::Constant, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u32_public_pow_u32_constant() {
        run_test::<u32, u32>(Mode::Public, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u32_public_pow_u32_public() {
        run_test::<u32, u32>(Mode::Public, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u32_public_pow_u32_private() {
        run_test::<u32, u32>(Mode::Public, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u32_private_pow_u32_constant() {
        run_test::<u32, u32>(Mode::Private, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u32_private_pow_u32_public() {
        run_test::<u32, u32>(Mode::Private, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u32_private_pow_u32_private() {
        run_test::<u32, u32>(Mode::Private, Mode::Private, count_is!(0, 0, 0, 0));
    }

    // Tests for i32 ^ u8.

    #[test]
    fn test_i32_constant_pow_u8_constant() {
        run_test::<i32, u8>(Mode::Constant, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i32_constant_pow_u8_public() {
        run_test::<i32, u8>(Mode::Constant, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i32_constant_pow_u8_private() {
        run_test::<i32, u8>(Mode::Constant, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i32_public_pow_u8_constant() {
        run_test::<i32, u8>(Mode::Public, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i32_public_pow_u8_public() {
        run_test::<i32, u8>(Mode::Public, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i32_public_pow_u8_private() {
        run_test::<i32, u8>(Mode::Public, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i32_private_pow_u8_constant() {
        run_test::<i32, u8>(Mode::Private, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i32_private_pow_u8_public() {
        run_test::<i32, u8>(Mode::Private, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i32_private_pow_u8_private() {
        run_test::<i32, u8>(Mode::Private, Mode::Private, count_is!(0, 0, 0, 0));
    }

    // Tests for i32 ^ u16.

    #[test]
    fn test_i32_constant_pow_u16_constant() {
        run_test::<i32, u16>(Mode::Constant, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i32_constant_pow_u16_public() {
        run_test::<i32, u16>(Mode::Constant, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i32_constant_pow_u16_private() {
        run_test::<i32, u16>(Mode::Constant, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i32_public_pow_u16_constant() {
        run_test::<i32, u16>(Mode::Public, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i32_public_pow_u16_public() {
        run_test::<i32, u16>(Mode::Public, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i32_public_pow_u16_private() {
        run_test::<i32, u16>(Mode::Public, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i32_private_pow_u16_constant() {
        run_test::<i32, u16>(Mode::Private, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i32_private_pow_u16_public() {
        run_test::<i32, u16>(Mode::Private, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i32_private_pow_u16_private() {
        run_test::<i32, u16>(Mode::Private, Mode::Private, count_is!(0, 0, 0, 0));
    }

    // Tests for i32 ^ u32.

    #[test]
    fn test_i32_constant_pow_u32_constant() {
        run_test::<i32, u32>(Mode::Constant, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i32_constant_pow_u32_public() {
        run_test::<i32, u32>(Mode::Constant, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i32_constant_pow_u32_private() {
        run_test::<i32, u32>(Mode::Constant, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i32_public_pow_u32_constant() {
        run_test::<i32, u32>(Mode::Public, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i32_public_pow_u32_public() {
        run_test::<i32, u32>(Mode::Public, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i32_public_pow_u32_private() {
        run_test::<i32, u32>(Mode::Public, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i32_private_pow_u32_constant() {
        run_test::<i32, u32>(Mode::Private, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i32_private_pow_u32_public() {
        run_test::<i32, u32>(Mode::Private, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i32_private_pow_u32_private() {
        run_test::<i32, u32>(Mode::Private, Mode::Private, count_is!(0, 0, 0, 0));
    }

    // Tests for u64 ^ u8.

    #[test]
    fn test_u64_constant_pow_u8_constant() {
        run_test::<u64, u8>(Mode::Constant, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u64_constant_pow_u8_public() {
        run_test::<u64, u8>(Mode::Constant, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u64_constant_pow_u8_private() {
        run_test::<u64, u8>(Mode::Constant, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u64_public_pow_u8_constant() {
        run_test::<u64, u8>(Mode::Public, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u64_public_pow_u8_public() {
        run_test::<u64, u8>(Mode::Public, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u64_public_pow_u8_private() {
        run_test::<u64, u8>(Mode::Public, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u64_private_pow_u8_constant() {
        run_test::<u64, u8>(Mode::Private, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u64_private_pow_u8_public() {
        run_test::<u64, u8>(Mode::Private, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u64_private_pow_u8_private() {
        run_test::<u64, u8>(Mode::Private, Mode::Private, count_is!(0, 0, 0, 0));
    }

    // Tests for u64 ^ u16.

    #[test]
    fn test_u64_constant_pow_u16_constant() {
        run_test::<u64, u16>(Mode::Constant, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u64_constant_pow_u16_public() {
        run_test::<u64, u16>(Mode::Constant, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u64_constant_pow_u16_private() {
        run_test::<u64, u16>(Mode::Constant, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u64_public_pow_u16_constant() {
        run_test::<u64, u16>(Mode::Public, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u64_public_pow_u16_public() {
        run_test::<u64, u16>(Mode::Public, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u64_public_pow_u16_private() {
        run_test::<u64, u16>(Mode::Public, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u64_private_pow_u16_constant() {
        run_test::<u64, u16>(Mode::Private, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u64_private_pow_u16_public() {
        run_test::<u64, u16>(Mode::Private, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u64_private_pow_u16_private() {
        run_test::<u64, u16>(Mode::Private, Mode::Private, count_is!(0, 0, 0, 0));
    }

    // Tests for u64 ^ u32.

    #[test]
    fn test_u64_constant_pow_u32_constant() {
        run_test::<u64, u32>(Mode::Constant, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u64_constant_pow_u32_public() {
        run_test::<u64, u32>(Mode::Constant, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u64_constant_pow_u32_private() {
        run_test::<u64, u32>(Mode::Constant, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u64_public_pow_u32_constant() {
        run_test::<u64, u32>(Mode::Public, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u64_public_pow_u32_public() {
        run_test::<u64, u32>(Mode::Public, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u64_public_pow_u32_private() {
        run_test::<u64, u32>(Mode::Public, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u64_private_pow_u32_constant() {
        run_test::<u64, u32>(Mode::Private, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u64_private_pow_u32_public() {
        run_test::<u64, u32>(Mode::Private, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u64_private_pow_u32_private() {
        run_test::<u64, u32>(Mode::Private, Mode::Private, count_is!(0, 0, 0, 0));
    }

    // Tests for i64 ^ u8.

    #[test]
    fn test_i64_constant_pow_u8_constant() {
        run_test::<i64, u8>(Mode::Constant, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i64_constant_pow_u8_public() {
        run_test::<i64, u8>(Mode::Constant, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i64_constant_pow_u8_private() {
        run_test::<i64, u8>(Mode::Constant, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i64_public_pow_u8_constant() {
        run_test::<i64, u8>(Mode::Public, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i64_public_pow_u8_public() {
        run_test::<i64, u8>(Mode::Public, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i64_public_pow_u8_private() {
        run_test::<i64, u8>(Mode::Public, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i64_private_pow_u8_constant() {
        run_test::<i64, u8>(Mode::Private, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i64_private_pow_u8_public() {
        run_test::<i64, u8>(Mode::Private, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i64_private_pow_u8_private() {
        run_test::<i64, u8>(Mode::Private, Mode::Private, count_is!(0, 0, 0, 0));
    }

    // Tests for i64 ^ u16.

    #[test]
    fn test_i64_constant_pow_u16_constant() {
        run_test::<i64, u16>(Mode::Constant, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i64_constant_pow_u16_public() {
        run_test::<i64, u16>(Mode::Constant, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i64_constant_pow_u16_private() {
        run_test::<i64, u16>(Mode::Constant, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i64_public_pow_u16_constant() {
        run_test::<i64, u16>(Mode::Public, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i64_public_pow_u16_public() {
        run_test::<i64, u16>(Mode::Public, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i64_public_pow_u16_private() {
        run_test::<i64, u16>(Mode::Public, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i64_private_pow_u16_constant() {
        run_test::<i64, u16>(Mode::Private, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i64_private_pow_u16_public() {
        run_test::<i64, u16>(Mode::Private, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i64_private_pow_u16_private() {
        run_test::<i64, u16>(Mode::Private, Mode::Private, count_is!(0, 0, 0, 0));
    }

    // Tests for i64 ^ u32.

    #[test]
    fn test_i64_constant_pow_u32_constant() {
        run_test::<i64, u32>(Mode::Constant, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i64_constant_pow_u32_public() {
        run_test::<i64, u32>(Mode::Constant, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i64_constant_pow_u32_private() {
        run_test::<i64, u32>(Mode::Constant, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i64_public_pow_u32_constant() {
        run_test::<i64, u32>(Mode::Public, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i64_public_pow_u32_public() {
        run_test::<i64, u32>(Mode::Public, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i64_public_pow_u32_private() {
        run_test::<i64, u32>(Mode::Public, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i64_private_pow_u32_constant() {
        run_test::<i64, u32>(Mode::Private, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i64_private_pow_u32_public() {
        run_test::<i64, u32>(Mode::Private, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i64_private_pow_u32_private() {
        run_test::<i64, u32>(Mode::Private, Mode::Private, count_is!(0, 0, 0, 0));
    }

    // Tests for u128 ^ u8.

    #[test]
    fn test_u128_constant_pow_u8_constant() {
        run_test::<u128, u8>(Mode::Constant, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u128_constant_pow_u8_public() {
        run_test::<u128, u8>(Mode::Constant, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u128_constant_pow_u8_private() {
        run_test::<u128, u8>(Mode::Constant, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u128_public_pow_u8_constant() {
        run_test::<u128, u8>(Mode::Public, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u128_public_pow_u8_public() {
        run_test::<u128, u8>(Mode::Public, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u128_public_pow_u8_private() {
        run_test::<u128, u8>(Mode::Public, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u128_private_pow_u8_constant() {
        run_test::<u128, u8>(Mode::Private, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u128_private_pow_u8_public() {
        run_test::<u128, u8>(Mode::Private, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u128_private_pow_u8_private() {
        run_test::<u128, u8>(Mode::Private, Mode::Private, count_is!(0, 0, 0, 0));
    }

    // Tests for u128 ^ u16.

    #[test]
    fn test_u128_constant_pow_u16_constant() {
        run_test::<u128, u16>(Mode::Constant, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u128_constant_pow_u16_public() {
        run_test::<u128, u16>(Mode::Constant, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u128_constant_pow_u16_private() {
        run_test::<u128, u16>(Mode::Constant, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u128_public_pow_u16_constant() {
        run_test::<u128, u16>(Mode::Public, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u128_public_pow_u16_public() {
        run_test::<u128, u16>(Mode::Public, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u128_public_pow_u16_private() {
        run_test::<u128, u16>(Mode::Public, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u128_private_pow_u16_constant() {
        run_test::<u128, u16>(Mode::Private, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u128_private_pow_u16_public() {
        run_test::<u128, u16>(Mode::Private, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u128_private_pow_u16_private() {
        run_test::<u128, u16>(Mode::Private, Mode::Private, count_is!(0, 0, 0, 0));
    }

    // Tests for u128 ^ u32.

    #[test]
    fn test_u128_constant_pow_u32_constant() {
        run_test::<u128, u32>(Mode::Constant, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u128_constant_pow_u32_public() {
        run_test::<u128, u32>(Mode::Constant, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u128_constant_pow_u32_private() {
        run_test::<u128, u32>(Mode::Constant, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u128_public_pow_u32_constant() {
        run_test::<u128, u32>(Mode::Public, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u128_public_pow_u32_public() {
        run_test::<u128, u32>(Mode::Public, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u128_public_pow_u32_private() {
        run_test::<u128, u32>(Mode::Public, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u128_private_pow_u32_constant() {
        run_test::<u128, u32>(Mode::Private, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u128_private_pow_u32_public() {
        run_test::<u128, u32>(Mode::Private, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_u128_private_pow_u32_private() {
        run_test::<u128, u32>(Mode::Private, Mode::Private, count_is!(0, 0, 0, 0));
    }

    // Tests for i128 ^ u8.

    #[test]
    fn test_i128_constant_pow_u8_constant() {
        run_test::<i128, u8>(Mode::Constant, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i128_constant_pow_u8_public() {
        run_test::<i128, u8>(Mode::Constant, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i128_constant_pow_u8_private() {
        run_test::<i128, u8>(Mode::Constant, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i128_public_pow_u8_constant() {
        run_test::<i128, u8>(Mode::Public, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i128_public_pow_u8_public() {
        run_test::<i128, u8>(Mode::Public, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i128_public_pow_u8_private() {
        run_test::<i128, u8>(Mode::Public, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i128_private_pow_u8_constant() {
        run_test::<i128, u8>(Mode::Private, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i128_private_pow_u8_public() {
        run_test::<i128, u8>(Mode::Private, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i128_private_pow_u8_private() {
        run_test::<i128, u8>(Mode::Private, Mode::Private, count_is!(0, 0, 0, 0));
    }

    // Tests for i128 ^ u16.

    #[test]
    fn test_i128_constant_pow_u16_constant() {
        run_test::<i128, u16>(Mode::Constant, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i128_constant_pow_u16_public() {
        run_test::<i128, u16>(Mode::Constant, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i128_constant_pow_u16_private() {
        run_test::<i128, u16>(Mode::Constant, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i128_public_pow_u16_constant() {
        run_test::<i128, u16>(Mode::Public, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i128_public_pow_u16_public() {
        run_test::<i128, u16>(Mode::Public, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i128_public_pow_u16_private() {
        run_test::<i128, u16>(Mode::Public, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i128_private_pow_u16_constant() {
        run_test::<i128, u16>(Mode::Private, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i128_private_pow_u16_public() {
        run_test::<i128, u16>(Mode::Private, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i128_private_pow_u16_private() {
        run_test::<i128, u16>(Mode::Private, Mode::Private, count_is!(0, 0, 0, 0));
    }

    // Tests for i128 ^ u32.

    #[test]
    fn test_i128_constant_pow_u32_constant() {
        run_test::<i128, u32>(Mode::Constant, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i128_constant_pow_u32_public() {
        run_test::<i128, u32>(Mode::Constant, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i128_constant_pow_u32_private() {
        run_test::<i128, u32>(Mode::Constant, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i128_public_pow_u32_constant() {
        run_test::<i128, u32>(Mode::Public, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i128_public_pow_u32_public() {
        run_test::<i128, u32>(Mode::Public, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i128_public_pow_u32_private() {
        run_test::<i128, u32>(Mode::Public, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i128_private_pow_u32_constant() {
        run_test::<i128, u32>(Mode::Private, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i128_private_pow_u32_public() {
        run_test::<i128, u32>(Mode::Private, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_i128_private_pow_u32_private() {
        run_test::<i128, u32>(Mode::Private, Mode::Private, count_is!(0, 0, 0, 0));
    }

    // Exhaustive tests for u8 ^ u8.

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_pow_u8_constant() {
        run_exhaustive_test::<u8, u8>(Mode::Constant, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_pow_u8_public() {
        run_exhaustive_test::<u8, u8>(Mode::Constant, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_pow_u8_private() {
        run_exhaustive_test::<u8, u8>(Mode::Constant, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_pow_u8_constant() {
        run_exhaustive_test::<u8, u8>(Mode::Public, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_pow_u8_public() {
        run_exhaustive_test::<u8, u8>(Mode::Public, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_pow_u8_private() {
        run_exhaustive_test::<u8, u8>(Mode::Public, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_pow_u8_constant() {
        run_exhaustive_test::<u8, u8>(Mode::Private, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_pow_u8_public() {
        run_exhaustive_test::<u8, u8>(Mode::Private, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_pow_u8_private() {
        run_exhaustive_test::<u8, u8>(Mode::Private, Mode::Private, count_is!(0, 0, 0, 0));
    }

    // Exhaustive tests for i8 ^ u8.

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_pow_u8_constant() {
        run_exhaustive_test::<i8, u8>(Mode::Constant, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_pow_u8_public() {
        run_exhaustive_test::<i8, u8>(Mode::Constant, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_pow_u8_private() {
        run_exhaustive_test::<i8, u8>(Mode::Constant, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_pow_u8_constant() {
        run_exhaustive_test::<i8, u8>(Mode::Public, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_pow_u8_public() {
        run_exhaustive_test::<i8, u8>(Mode::Public, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_pow_u8_private() {
        run_exhaustive_test::<i8, u8>(Mode::Public, Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_pow_u8_constant() {
        run_exhaustive_test::<i8, u8>(Mode::Private, Mode::Constant, count_is!(0, 0, 0, 0));
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_pow_u8_public() {
        run_exhaustive_test::<i8, u8>(Mode::Private, Mode::Public, count_is!(0, 0, 0, 0));
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_pow_u8_private() {
        run_exhaustive_test::<i8, u8>(Mode::Private, Mode::Private, count_is!(0, 0, 0, 0));
    }
}
