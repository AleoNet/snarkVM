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

impl<E: Environment, I: IntegerType, M: Magnitude> ShlWrapped<Integer<E, M>> for Integer<E, I> {
    type Output = Self;

    #[inline]
    fn shl_wrapped(&self, rhs: &Integer<E, M>) -> Self::Output {
        // Determine the variable mode.
        if self.is_constant() && rhs.is_constant() {
            // Note: Casting `rhs` to a `u32` is safe since `Magnitude`s can only be `u8`, `u16`, or `u32`.
            witness!(|self, rhs| console::Integer::new(self.wrapping_shl(rhs.to_u32().unwrap())))
        } else {
            // Index of the first upper bit of rhs that we mask.
            let first_upper_bit_index = I::BITS.trailing_zeros() as usize;

            // Perform the left shift operation by exponentiation and multiplication.
            // By masking the upper bits, we have that rhs < I::BITS.
            // Therefore, 2^{rhs} < Integer::MAX.

            // Zero-extend `rhs` by `8`.
            let mut bits_le = rhs.bits_le[..first_upper_bit_index].to_vec();
            bits_le.extend(core::iter::repeat(Boolean::constant(false)).take(8));

            // Use U8 for the exponent as it costs fewer constraints.
            let rhs_as_u8 = U8 { bits_le, phantom: Default::default() };

            if rhs_as_u8.is_constant() {
                // If the shift amount is a constant, then we can manually shift in bits and truncate the result.
                let shift_amount = rhs_as_u8.eject_value();
                let mut bits_le = vec![Boolean::constant(false); *shift_amount as usize];

                bits_le.extend_from_slice(&self.bits_le);
                bits_le.truncate(I::BITS as usize);

                Self { bits_le, phantom: Default::default() }
            } else {
                // Calculate the value of the shift directly in the field.
                // Since 2^{rhs} < Integer::MAX, we know that the operation will not overflow Integer::MAX or the field modulus.
                let two = Field::one() + Field::one();
                let mut shift_in_field = Field::one();
                for bit in rhs.bits_le[..first_upper_bit_index].iter().rev() {
                    shift_in_field = shift_in_field.square();
                    shift_in_field = Field::ternary(bit, &(&shift_in_field * &two), &shift_in_field);
                }
                // TODO (@pranav) Avoid initializing the integer.
                let shift_as_multiplicand =
                    Self { bits_le: shift_in_field.to_lower_bits_le(I::BITS as usize), phantom: Default::default() };
                self.mul_wrapped(&shift_as_multiplicand)
            }
        }
    }
}

impl<E: Environment, I: IntegerType, M: Magnitude> Metrics<dyn ShlWrapped<Integer<E, M>, Output = Integer<E, I>>>
    for Integer<E, I>
{
    type Case = (Mode, Mode);

    fn count(case: &Self::Case) -> Count {
        // A quick hack that matches `(u8 -> 0, u16 -> 1, u32 -> 2, u64 -> 3, u128 -> 4)`.
        let index = |num_bits: u64| match [8, 16, 32, 64, 128].iter().position(|&bits| bits == num_bits) {
            Some(index) => index as u64,
            None => E::halt(format!("Integer of {num_bits} bits is not supported")),
        };

        match (case.0, case.1) {
            (Mode::Constant, Mode::Constant) => Count::is(I::BITS, 0, 0, 0),
            (_, Mode::Constant) => Count::is(0, 0, 0, 0),
            (Mode::Constant, _) => Count::is(
                0,
                0,
                (2 * I::BITS) + (I::BITS / 2) + (2 * index(I::BITS)) + 5,
                (2 * I::BITS) + (I::BITS / 2) + (2 * index(I::BITS)) + 7,
            ),
            (_, _) => Count::is(
                0,
                0,
                (2 * I::BITS) + (I::BITS / 2) + (2 * index(I::BITS)) + 8,
                (2 * I::BITS) + (I::BITS / 2) + (2 * index(I::BITS)) + 10,
            ),
        }
    }
}

impl<E: Environment, I: IntegerType, M: Magnitude> OutputMode<dyn ShlWrapped<Integer<E, M>, Output = Integer<E, I>>>
    for Integer<E, I>
{
    type Case = (Mode, Mode);

    fn output_mode(case: &Self::Case) -> Mode {
        match (case.0, case.1) {
            (Mode::Constant, Mode::Constant) => Mode::Constant,
            (mode_a, Mode::Constant) => mode_a,
            (_, _) => Mode::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    use core::{ops::RangeInclusive, panic::RefUnwindSafe};

    const ITERATIONS: u64 = 32;

    fn check_shl<I: IntegerType + RefUnwindSafe, M: Magnitude + RefUnwindSafe>(
        name: &str,
        first: console::Integer<<Circuit as Environment>::Network, I>,
        second: console::Integer<<Circuit as Environment>::Network, M>,
        mode_a: Mode,
        mode_b: Mode,
    ) {
        let expected = first.wrapping_shl(second.to_u32().unwrap());
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, M>::new(mode_b, second);
        Circuit::scope(name, || {
            let candidate = a.shl_wrapped(&b);
            assert_eq!(expected, *candidate.eject_value());
            assert_eq!(console::Integer::new(expected), candidate.eject_value());
            assert_count!(ShlWrapped(Integer<I>, Integer<M>) => Integer<I>, &(mode_a, mode_b));
            assert_output_mode!(ShlWrapped(Integer<I>, Integer<M>) => Integer<I>, &(mode_a, mode_b), candidate);
        });
        Circuit::reset();
    }

    fn run_test<I: IntegerType + RefUnwindSafe, M: Magnitude + RefUnwindSafe>(mode_a: Mode, mode_b: Mode) {
        for i in 0..ITERATIONS {
            let first = Uniform::rand(&mut test_rng());
            let second = Uniform::rand(&mut test_rng());

            let name = format!("Shl: {} << {} {}", mode_a, mode_b, i);
            check_shl::<I, M>(&name, first, second, mode_a, mode_b);

            // Check that shift left by one is computed correctly.
            let name = format!("Double: {} << {} {}", mode_a, mode_b, i);
            check_shl::<I, M>(&name, first, console::Integer::one(), mode_a, mode_b);

            // Check that shift left by two is computed correctly.
            let name = format!("Quadruple: {} << {} {}", mode_a, mode_b, i);
            check_shl::<I, M>(&name, first, console::Integer::one() + console::Integer::one(), mode_a, mode_b);
        }
    }

    fn run_exhaustive_test<I: IntegerType + RefUnwindSafe, M: Magnitude + RefUnwindSafe>(mode_a: Mode, mode_b: Mode)
    where
        RangeInclusive<I>: Iterator<Item = I>,
        RangeInclusive<M>: Iterator<Item = M>,
    {
        for first in I::MIN..=I::MAX {
            for second in M::MIN..=M::MAX {
                let first = console::Integer::<_, I>::new(first);
                let second = console::Integer::<_, M>::new(second);

                let name = format!("Shl: ({} << {})", first, second);
                check_shl::<I, M>(&name, first, second, mode_a, mode_b);
            }
        }
    }

    test_integer_binary!(run_test, i8, u8, shl);
    test_integer_binary!(run_test, i8, u16, shl);
    test_integer_binary!(run_test, i8, u32, shl);

    test_integer_binary!(run_test, i16, u8, shl);
    test_integer_binary!(run_test, i16, u16, shl);
    test_integer_binary!(run_test, i16, u32, shl);

    test_integer_binary!(run_test, i32, u8, shl);
    test_integer_binary!(run_test, i32, u16, shl);
    test_integer_binary!(run_test, i32, u32, shl);

    test_integer_binary!(run_test, i64, u8, shl);
    test_integer_binary!(run_test, i64, u16, shl);
    test_integer_binary!(run_test, i64, u32, shl);

    test_integer_binary!(run_test, i128, u8, shl);
    test_integer_binary!(run_test, i128, u16, shl);
    test_integer_binary!(run_test, i128, u32, shl);

    test_integer_binary!(run_test, u8, u8, shl);
    test_integer_binary!(run_test, u8, u16, shl);
    test_integer_binary!(run_test, u8, u32, shl);

    test_integer_binary!(run_test, u16, u8, shl);
    test_integer_binary!(run_test, u16, u16, shl);
    test_integer_binary!(run_test, u16, u32, shl);

    test_integer_binary!(run_test, u32, u8, shl);
    test_integer_binary!(run_test, u32, u16, shl);
    test_integer_binary!(run_test, u32, u32, shl);

    test_integer_binary!(run_test, u64, u8, shl);
    test_integer_binary!(run_test, u64, u16, shl);
    test_integer_binary!(run_test, u64, u32, shl);

    test_integer_binary!(run_test, u128, u8, shl);
    test_integer_binary!(run_test, u128, u16, shl);
    test_integer_binary!(run_test, u128, u32, shl);

    test_integer_binary!(#[ignore], run_exhaustive_test, u8, u8, shl, exhaustive);
    test_integer_binary!(#[ignore], run_exhaustive_test, i8, u8, shl, exhaustive);
}
