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

impl<E: Environment, I: IntegerType, M: Magnitude> ShrWrapped<Integer<E, M>> for Integer<E, I> {
    type Output = Self;

    #[inline]
    fn shr_wrapped(&self, rhs: &Integer<E, M>) -> Self::Output {
        // Determine the variable mode.
        if self.is_constant() && rhs.is_constant() {
            // Note: Casting `rhs` to `u32` is safe since `Magnitude`s can only be `u8`, `u16`, or `u32`.
            witness!(|self, rhs| console::Integer::new(self.wrapping_shr(rhs.to_u32().unwrap())))
        } else {
            // Index of the first upper bit of rhs that we mask.
            let first_upper_bit_index = I::BITS.trailing_zeros() as usize;

            // Perform the right shift operation by exponentiation and multiplication.
            // By masking the upper bits, we have that rhs < I::BITS.
            // Therefore, 2^{rhs} < Integer::MAX.
            let mut lower_rhs_bits = Vec::with_capacity(8);
            lower_rhs_bits.extend_from_slice(&rhs.bits_le[..first_upper_bit_index]);
            lower_rhs_bits.resize(8, Boolean::constant(false));

            // Use U8 for the exponent as it costs fewer constraints.
            let rhs_as_u8 = U8 { bits_le: lower_rhs_bits, phantom: Default::default() };

            if rhs_as_u8.is_constant() {
                // If the shift amount is a constant, then we can manually shift in bits and truncate the result.
                let shift_amount = *rhs_as_u8.eject_value() as usize;

                let mut bits_le = Vec::with_capacity(I::BITS as usize + shift_amount);
                bits_le.extend_from_slice(&self.bits_le);

                match I::is_signed() {
                    // Sign-extend `self` by `shift_amount`.
                    true => bits_le.extend(core::iter::repeat(self.msb().clone()).take(shift_amount)),
                    // Zero-extend `self` by `shift_amount`.
                    false => bits_le.extend(core::iter::repeat(Boolean::constant(false)).take(shift_amount)),
                };

                bits_le.reverse();
                bits_le.truncate(I::BITS as usize);
                bits_le.reverse();

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
                let shift_as_divisor =
                    Self { bits_le: shift_in_field.to_lower_bits_le(I::BITS as usize), phantom: Default::default() };

                if I::is_signed() {
                    // Divide the absolute value of `self` and `shift` (as a divisor) in the base field.
                    let dividend_unsigned = self.abs_wrapped().cast_as_dual();
                    let divisor_unsigned = shift_as_divisor.cast_as_dual();

                    let dividend = dividend_unsigned.eject_value();
                    let divisor = divisor_unsigned.eject_value();

                    // Wrapping operations are safe since unsigned division never overflows.
                    let quotient_unsigned = Integer::<E, I::Dual>::new(
                        Mode::Private,
                        console::Integer::new(dividend.wrapping_div(&divisor)),
                    );
                    let remainder_unsigned = Integer::<E, I::Dual>::new(
                        Mode::Private,
                        console::Integer::new(dividend.wrapping_rem(&divisor)),
                    );

                    // Ensure that Euclidean division holds for these values in the base field.
                    let remainder_field = remainder_unsigned.to_field();
                    E::assert_eq(
                        dividend_unsigned.to_field(),
                        quotient_unsigned.to_field() * divisor_unsigned.to_field() + &remainder_field,
                    );

                    // Ensure that the remainder is less than the divisor.
                    E::assert(remainder_unsigned.is_less_than(&divisor_unsigned));

                    // Note that quotient <= |console::Integer::MIN|, since the dividend <= |console::Integer::MIN| and 0 <= quotient <= dividend.
                    let quotient = Self { bits_le: quotient_unsigned.bits_le, phantom: Default::default() };
                    let negated_quotient = &(!&quotient).add_wrapped(&Self::one());

                    // Arithmetic shift uses a different rounding mode than division.
                    let rounded_negated_quotient = Self::ternary(
                        &remainder_field.is_equal(&Field::zero()),
                        negated_quotient,
                        &(negated_quotient).sub_wrapped(&Self::one()),
                    );

                    Self::ternary(self.msb(), &rounded_negated_quotient, &quotient)
                } else {
                    self.div_wrapped(&shift_as_divisor)
                }
            }
        }
    }
}

impl<E: Environment, I: IntegerType, M: Magnitude> Metrics<dyn ShrWrapped<Integer<E, M>, Output = Integer<E, I>>>
    for Integer<E, I>
{
    type Case = (Mode, Mode);

    fn count(case: &Self::Case) -> Count {
        // A quick hack that matches `(u8 -> 0, u16 -> 1, u32 -> 2, u64 -> 3, u128 -> 4)`.
        let index = |num_bits: u64| match [8, 16, 32, 64, 128].iter().position(|&bits| bits == num_bits) {
            Some(index) => index as u64,
            None => E::halt(format!("Integer of {num_bits} bits is not supported")),
        };

        match I::is_signed() {
            // Signed case
            true => match (case.0, case.1) {
                (Mode::Constant, Mode::Constant) => Count::is(I::BITS, 0, 0, 0),
                (_, Mode::Constant) => Count::is(0, 0, 0, 0),
                (Mode::Constant, _) => Count::is(
                    4 * I::BITS,
                    0,
                    (6 * I::BITS) + (2 * index(I::BITS)) + 9,
                    (6 * I::BITS) + (2 * index(I::BITS)) + 14,
                ),
                (_, _) => Count::is(
                    3 * I::BITS,
                    0,
                    (9 * I::BITS) + (2 * index(I::BITS)) + 10,
                    (9 * I::BITS) + (2 * index(I::BITS)) + 16,
                ),
            },
            // Unsigned case
            false => match (case.0, case.1) {
                (Mode::Constant, Mode::Constant) => Count::is(I::BITS, 0, 0, 0),
                (_, Mode::Constant) => Count::is(0, 0, 0, 0),
                (Mode::Constant, _) | (_, _) => {
                    Count::is(0, 0, (3 * I::BITS) + (2 * index(I::BITS)) + 5, (3 * I::BITS) + (2 * index(I::BITS)) + 7)
                }
            },
        }
    }
}

impl<E: Environment, I: IntegerType, M: Magnitude> OutputMode<dyn ShrWrapped<Integer<E, M>, Output = Integer<E, I>>>
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

    fn check_shr<I: IntegerType + RefUnwindSafe, M: Magnitude + RefUnwindSafe>(
        name: &str,
        first: console::Integer<<Circuit as Environment>::Network, I>,
        second: console::Integer<<Circuit as Environment>::Network, M>,
        mode_a: Mode,
        mode_b: Mode,
    ) {
        let expected = first.wrapping_shr(second.to_u32().unwrap());
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, M>::new(mode_b, second);
        Circuit::scope(name, || {
            let candidate = a.shr_wrapped(&b);
            assert_eq!(expected, *candidate.eject_value());
            assert_eq!(console::Integer::new(expected), candidate.eject_value());
            // assert_count!(ShrWrapped(Integer<I>, Integer<M>) => Integer<I>, &(mode_a, mode_b));
            // assert_output_mode!(ShrWrapped(Integer<I>, Integer<M>) => Integer<I>, &(mode_a, mode_b), candidate);
            assert!(Circuit::is_satisfied_in_scope(), "(is_satisfied_in_scope)");
        });
        Circuit::reset();
    }

    fn run_test<I: IntegerType + RefUnwindSafe, M: Magnitude + RefUnwindSafe>(mode_a: Mode, mode_b: Mode) {
        for i in 0..ITERATIONS {
            let first = Uniform::rand(&mut test_rng());
            let second = Uniform::rand(&mut test_rng());

            let name = format!("Shr: {} >> {} {}", mode_a, mode_b, i);
            check_shr::<I, M>(&name, first, second, mode_a, mode_b);

            // Check that shift right by one is computed correctly.
            let name = format!("Half: {} >> {} {}", mode_a, mode_b, i);
            check_shr::<I, M>(&name, first, console::Integer::one(), mode_a, mode_b);
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

                let name = format!("Shr: ({} >> {})", first, second);
                check_shr::<I, M>(&name, first, second, mode_a, mode_b);
            }
        }
    }

    test_integer_binary!(run_test, i8, u8, shr);
    test_integer_binary!(run_test, i8, u16, shr);
    test_integer_binary!(run_test, i8, u32, shr);

    test_integer_binary!(run_test, i16, u8, shr);
    test_integer_binary!(run_test, i16, u16, shr);
    test_integer_binary!(run_test, i16, u32, shr);

    test_integer_binary!(run_test, i32, u8, shr);
    test_integer_binary!(run_test, i32, u16, shr);
    test_integer_binary!(run_test, i32, u32, shr);

    test_integer_binary!(run_test, i64, u8, shr);
    test_integer_binary!(run_test, i64, u16, shr);
    test_integer_binary!(run_test, i64, u32, shr);

    test_integer_binary!(run_test, i128, u8, shr);
    test_integer_binary!(run_test, i128, u16, shr);
    test_integer_binary!(run_test, i128, u32, shr);

    test_integer_binary!(run_test, u8, u8, shr);
    test_integer_binary!(run_test, u8, u16, shr);
    test_integer_binary!(run_test, u8, u32, shr);

    test_integer_binary!(run_test, u16, u8, shr);
    test_integer_binary!(run_test, u16, u16, shr);
    test_integer_binary!(run_test, u16, u32, shr);

    test_integer_binary!(run_test, u32, u8, shr);
    test_integer_binary!(run_test, u32, u16, shr);
    test_integer_binary!(run_test, u32, u32, shr);

    test_integer_binary!(run_test, u64, u8, shr);
    test_integer_binary!(run_test, u64, u16, shr);
    test_integer_binary!(run_test, u64, u32, shr);

    test_integer_binary!(run_test, u128, u8, shr);
    test_integer_binary!(run_test, u128, u16, shr);
    test_integer_binary!(run_test, u128, u32, shr);

    test_integer_binary!(#[ignore], run_exhaustive_test, u8, u8, shr, exhaustive);
    test_integer_binary!(#[ignore], run_exhaustive_test, i8, u8, shr, exhaustive);
}
