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

impl<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize> Ternary
    for Signed<E, I, U, SIZE>
{
    type Boolean = Boolean<E>;
    type Output = Self;

    /// Returns `first` if `condition` is `true`, otherwise returns `second`.
    fn ternary(condition: &Self::Boolean, first: &Self, second: &Self) -> Self::Output {
        let mut result_bits = Vec::with_capacity(SIZE);
        for (first_bit, second_bit) in first.bits_le.iter().zip(second.bits_le.iter()) {
            result_bits.push(Ternary::ternary(condition, first_bit, second_bit));
        }
        Signed::from_bits(result_bits)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{integers::signed::test_utilities::check_operation, Circuit};
    use snarkvm_utilities::UniformRand;

    use rand::{
        distributions::{Distribution, Standard},
        thread_rng,
    };

    const ITERATIONS: usize = 10;

    fn run_test<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize>(
        iterations: usize,
        condition: bool,
        mode_condition: Mode,
        mode_a: Mode,
        mode_b: Mode,
        circuit_properties: Option<(usize, usize, usize, usize)>,
    ) where
        Standard: Distribution<I>,
    {
        for i in 0..iterations {
            let first: I = UniformRand::rand(&mut thread_rng());
            let second: I = UniformRand::rand(&mut thread_rng());

            let expected = if condition { first } else { second };
            let a = Signed::new(mode_a, first);
            let b = Signed::new(mode_b, second);
            let name = format!("Ternary {}", i);
            let compute_candidate = || Signed::ternary(&Boolean::new(mode_condition, condition), &a, &b);
            check_operation::<E, I, U, SIZE>(&name, expected, &compute_candidate, circuit_properties);
        }
    }

    // TODO (@pranav) Fix expected circuit properties for all tests

    #[test]
    #[rustfmt::skip]
    fn test_i8_ternary_all_modes() {
        // Boolean(Constant, false)
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, false, Mode::Constant, Mode::Constant, Mode::Constant, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, false, Mode::Constant, Mode::Constant, Mode::Public, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, false, Mode::Constant, Mode::Constant, Mode::Private, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, false, Mode::Constant, Mode::Public, Mode::Constant, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, false, Mode::Constant, Mode::Public, Mode::Public, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, false, Mode::Constant, Mode::Public, Mode::Private, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, false, Mode::Constant, Mode::Private, Mode::Constant, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, false, Mode::Constant, Mode::Private, Mode::Public, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, false, Mode::Constant, Mode::Private, Mode::Private, Some((8, 0, 0, 0)));

        // Boolean(Constant, true)
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, true, Mode::Constant, Mode::Constant, Mode::Constant, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, true, Mode::Constant, Mode::Constant, Mode::Public, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, true, Mode::Constant, Mode::Constant, Mode::Private, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, true, Mode::Constant, Mode::Public, Mode::Constant, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, true, Mode::Constant, Mode::Public, Mode::Public, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, true, Mode::Constant, Mode::Public, Mode::Private, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, true, Mode::Constant, Mode::Private, Mode::Constant, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, true, Mode::Constant, Mode::Private, Mode::Public, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, true, Mode::Constant, Mode::Private, Mode::Private, Some((8, 0, 0, 0)));

        // Boolean(Public, false)
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, false, Mode::Public, Mode::Constant, Mode::Constant, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, false, Mode::Public, Mode::Constant, Mode::Public, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, false, Mode::Public, Mode::Constant, Mode::Private, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, false, Mode::Public, Mode::Public, Mode::Constant, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, false, Mode::Public, Mode::Public, Mode::Public, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, false, Mode::Public, Mode::Public, Mode::Private, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, false, Mode::Public, Mode::Private, Mode::Constant, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, false, Mode::Public, Mode::Private, Mode::Public, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, false, Mode::Public, Mode::Private, Mode::Private, Some((8, 0, 0, 0)));

        // Boolean(Public, true)
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, true, Mode::Public, Mode::Constant, Mode::Constant, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, true, Mode::Public, Mode::Constant, Mode::Public, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, true, Mode::Public, Mode::Constant, Mode::Private, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, true, Mode::Public, Mode::Public, Mode::Constant, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, true, Mode::Public, Mode::Public, Mode::Public, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, true, Mode::Public, Mode::Public, Mode::Private, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, true, Mode::Public, Mode::Private, Mode::Constant, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, true, Mode::Public, Mode::Private, Mode::Public, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, true, Mode::Public, Mode::Private, Mode::Private, Some((8, 0, 0, 0)));

        // Boolean(Private, false)
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, false, Mode::Private, Mode::Constant, Mode::Constant, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, false, Mode::Private, Mode::Constant, Mode::Public, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, false, Mode::Private, Mode::Constant, Mode::Private, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, false, Mode::Private, Mode::Public, Mode::Constant, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, false, Mode::Private, Mode::Public, Mode::Public, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, false, Mode::Private, Mode::Public, Mode::Private, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, false, Mode::Private, Mode::Private, Mode::Constant, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, false, Mode::Private, Mode::Private, Mode::Public, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, false, Mode::Private, Mode::Private, Mode::Private, Some((8, 0, 0, 0)));

        // Boolean(Private, true)
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, true, Mode::Private, Mode::Constant, Mode::Constant, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, true, Mode::Private, Mode::Constant, Mode::Public, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, true, Mode::Private, Mode::Constant, Mode::Private, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, true, Mode::Private, Mode::Public, Mode::Constant, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, true, Mode::Private, Mode::Public, Mode::Public, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, true, Mode::Private, Mode::Public, Mode::Private, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, true, Mode::Private, Mode::Private, Mode::Constant, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, true, Mode::Private, Mode::Private, Mode::Public, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, true, Mode::Private, Mode::Private, Mode::Private, Some((8, 0, 0, 0)));
    }

    #[test]
    #[rustfmt::skip]
    fn test_i16_ternary_all_modes() {
        // Boolean(Constant, false)
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, false, Mode::Constant, Mode::Constant, Mode::Constant, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, false, Mode::Constant, Mode::Constant, Mode::Public, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, false, Mode::Constant, Mode::Constant, Mode::Private, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, false, Mode::Constant, Mode::Public, Mode::Constant, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, false, Mode::Constant, Mode::Public, Mode::Public, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, false, Mode::Constant, Mode::Public, Mode::Private, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, false, Mode::Constant, Mode::Private, Mode::Constant, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, false, Mode::Constant, Mode::Private, Mode::Public, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, false, Mode::Constant, Mode::Private, Mode::Private, Some((16, 0, 0, 0)));

        // Boolean(Constant, true)
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, true, Mode::Constant, Mode::Constant, Mode::Constant, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, true, Mode::Constant, Mode::Constant, Mode::Public, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, true, Mode::Constant, Mode::Constant, Mode::Private, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, true, Mode::Constant, Mode::Public, Mode::Constant, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, true, Mode::Constant, Mode::Public, Mode::Public, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, true, Mode::Constant, Mode::Public, Mode::Private, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, true, Mode::Constant, Mode::Private, Mode::Constant, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, true, Mode::Constant, Mode::Private, Mode::Public, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, true, Mode::Constant, Mode::Private, Mode::Private, Some((16, 0, 0, 0)));

        // Boolean(Public, false)
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, false, Mode::Public, Mode::Constant, Mode::Constant, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, false, Mode::Public, Mode::Constant, Mode::Public, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, false, Mode::Public, Mode::Constant, Mode::Private, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, false, Mode::Public, Mode::Public, Mode::Constant, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, false, Mode::Public, Mode::Public, Mode::Public, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, false, Mode::Public, Mode::Public, Mode::Private, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, false, Mode::Public, Mode::Private, Mode::Constant, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, false, Mode::Public, Mode::Private, Mode::Public, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, false, Mode::Public, Mode::Private, Mode::Private, Some((16, 0, 0, 0)));

        // Boolean(Public, true)
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, true, Mode::Public, Mode::Constant, Mode::Constant, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, true, Mode::Public, Mode::Constant, Mode::Public, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, true, Mode::Public, Mode::Constant, Mode::Private, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, true, Mode::Public, Mode::Public, Mode::Constant, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, true, Mode::Public, Mode::Public, Mode::Public, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, true, Mode::Public, Mode::Public, Mode::Private, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, true, Mode::Public, Mode::Private, Mode::Constant, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, true, Mode::Public, Mode::Private, Mode::Public, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, true, Mode::Public, Mode::Private, Mode::Private, Some((16, 0, 0, 0)));

        // Boolean(Private, false)
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, false, Mode::Private, Mode::Constant, Mode::Constant, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, false, Mode::Private, Mode::Constant, Mode::Public, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, false, Mode::Private, Mode::Constant, Mode::Private, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, false, Mode::Private, Mode::Public, Mode::Constant, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, false, Mode::Private, Mode::Public, Mode::Public, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, false, Mode::Private, Mode::Public, Mode::Private, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, false, Mode::Private, Mode::Private, Mode::Constant, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, false, Mode::Private, Mode::Private, Mode::Public, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, false, Mode::Private, Mode::Private, Mode::Private, Some((16, 0, 0, 0)));

        // Boolean(Private, true)
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, true, Mode::Private, Mode::Constant, Mode::Constant, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, true, Mode::Private, Mode::Constant, Mode::Public, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, true, Mode::Private, Mode::Constant, Mode::Private, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, true, Mode::Private, Mode::Public, Mode::Constant, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, true, Mode::Private, Mode::Public, Mode::Public, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, true, Mode::Private, Mode::Public, Mode::Private, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, true, Mode::Private, Mode::Private, Mode::Constant, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, true, Mode::Private, Mode::Private, Mode::Public, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, true, Mode::Private, Mode::Private, Mode::Private, Some((16, 0, 0, 0)));
    }

    #[test]
    #[rustfmt::skip]
    fn test_i32_ternary_all_modes() {
        // Boolean(Constant, false)
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, false, Mode::Constant, Mode::Constant, Mode::Constant, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, false, Mode::Constant, Mode::Constant, Mode::Public, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, false, Mode::Constant, Mode::Constant, Mode::Private, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, false, Mode::Constant, Mode::Public, Mode::Constant, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, false, Mode::Constant, Mode::Public, Mode::Public, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, false, Mode::Constant, Mode::Public, Mode::Private, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, false, Mode::Constant, Mode::Private, Mode::Constant, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, false, Mode::Constant, Mode::Private, Mode::Public, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, false, Mode::Constant, Mode::Private, Mode::Private, Some((32, 0, 0, 0)));

        // Boolean(Constant, true)
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, true, Mode::Constant, Mode::Constant, Mode::Constant, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, true, Mode::Constant, Mode::Constant, Mode::Public, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, true, Mode::Constant, Mode::Constant, Mode::Private, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, true, Mode::Constant, Mode::Public, Mode::Constant, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, true, Mode::Constant, Mode::Public, Mode::Public, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, true, Mode::Constant, Mode::Public, Mode::Private, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, true, Mode::Constant, Mode::Private, Mode::Constant, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, true, Mode::Constant, Mode::Private, Mode::Public, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, true, Mode::Constant, Mode::Private, Mode::Private, Some((32, 0, 0, 0)));

        // Boolean(Public, false)
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, false, Mode::Public, Mode::Constant, Mode::Constant, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, false, Mode::Public, Mode::Constant, Mode::Public, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, false, Mode::Public, Mode::Constant, Mode::Private, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, false, Mode::Public, Mode::Public, Mode::Constant, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, false, Mode::Public, Mode::Public, Mode::Public, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, false, Mode::Public, Mode::Public, Mode::Private, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, false, Mode::Public, Mode::Private, Mode::Constant, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, false, Mode::Public, Mode::Private, Mode::Public, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, false, Mode::Public, Mode::Private, Mode::Private, Some((32, 0, 0, 0)));

        // Boolean(Public, true)
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, true, Mode::Public, Mode::Constant, Mode::Constant, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, true, Mode::Public, Mode::Constant, Mode::Public, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, true, Mode::Public, Mode::Constant, Mode::Private, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, true, Mode::Public, Mode::Public, Mode::Constant, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, true, Mode::Public, Mode::Public, Mode::Public, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, true, Mode::Public, Mode::Public, Mode::Private, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, true, Mode::Public, Mode::Private, Mode::Constant, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, true, Mode::Public, Mode::Private, Mode::Public, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, true, Mode::Public, Mode::Private, Mode::Private, Some((32, 0, 0, 0)));

        // Boolean(Private, false)
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, false, Mode::Private, Mode::Constant, Mode::Constant, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, false, Mode::Private, Mode::Constant, Mode::Public, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, false, Mode::Private, Mode::Constant, Mode::Private, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, false, Mode::Private, Mode::Public, Mode::Constant, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, false, Mode::Private, Mode::Public, Mode::Public, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, false, Mode::Private, Mode::Public, Mode::Private, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, false, Mode::Private, Mode::Private, Mode::Constant, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, false, Mode::Private, Mode::Private, Mode::Public, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, false, Mode::Private, Mode::Private, Mode::Private, Some((32, 0, 0, 0)));

        // Boolean(Private, true)
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, true, Mode::Private, Mode::Constant, Mode::Constant, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, true, Mode::Private, Mode::Constant, Mode::Public, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, true, Mode::Private, Mode::Constant, Mode::Private, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, true, Mode::Private, Mode::Public, Mode::Constant, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, true, Mode::Private, Mode::Public, Mode::Public, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, true, Mode::Private, Mode::Public, Mode::Private, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, true, Mode::Private, Mode::Private, Mode::Constant, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, true, Mode::Private, Mode::Private, Mode::Public, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, true, Mode::Private, Mode::Private, Mode::Private, Some((32, 0, 0, 0)));
    }

    #[test]
    #[rustfmt::skip]
    fn test_i64_ternary_all_modes() {
        // Boolean(Constant, false)
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, false, Mode::Constant, Mode::Constant, Mode::Constant, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, false, Mode::Constant, Mode::Constant, Mode::Public, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, false, Mode::Constant, Mode::Constant, Mode::Private, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, false, Mode::Constant, Mode::Public, Mode::Constant, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, false, Mode::Constant, Mode::Public, Mode::Public, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, false, Mode::Constant, Mode::Public, Mode::Private, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, false, Mode::Constant, Mode::Private, Mode::Constant, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, false, Mode::Constant, Mode::Private, Mode::Public, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, false, Mode::Constant, Mode::Private, Mode::Private, Some((64, 0, 0, 0)));

        // Boolean(Constant, true)
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, true, Mode::Constant, Mode::Constant, Mode::Constant, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, true, Mode::Constant, Mode::Constant, Mode::Public, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, true, Mode::Constant, Mode::Constant, Mode::Private, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, true, Mode::Constant, Mode::Public, Mode::Constant, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, true, Mode::Constant, Mode::Public, Mode::Public, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, true, Mode::Constant, Mode::Public, Mode::Private, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, true, Mode::Constant, Mode::Private, Mode::Constant, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, true, Mode::Constant, Mode::Private, Mode::Public, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, true, Mode::Constant, Mode::Private, Mode::Private, Some((64, 0, 0, 0)));

        // Boolean(Public, false)
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, false, Mode::Public, Mode::Constant, Mode::Constant, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, false, Mode::Public, Mode::Constant, Mode::Public, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, false, Mode::Public, Mode::Constant, Mode::Private, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, false, Mode::Public, Mode::Public, Mode::Constant, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, false, Mode::Public, Mode::Public, Mode::Public, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, false, Mode::Public, Mode::Public, Mode::Private, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, false, Mode::Public, Mode::Private, Mode::Constant, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, false, Mode::Public, Mode::Private, Mode::Public, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, false, Mode::Public, Mode::Private, Mode::Private, Some((64, 0, 0, 0)));

        // Boolean(Public, true)
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, true, Mode::Public, Mode::Constant, Mode::Constant, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, true, Mode::Public, Mode::Constant, Mode::Public, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, true, Mode::Public, Mode::Constant, Mode::Private, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, true, Mode::Public, Mode::Public, Mode::Constant, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, true, Mode::Public, Mode::Public, Mode::Public, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, true, Mode::Public, Mode::Public, Mode::Private, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, true, Mode::Public, Mode::Private, Mode::Constant, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, true, Mode::Public, Mode::Private, Mode::Public, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, true, Mode::Public, Mode::Private, Mode::Private, Some((64, 0, 0, 0)));

        // Boolean(Private, false)
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, false, Mode::Private, Mode::Constant, Mode::Constant, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, false, Mode::Private, Mode::Constant, Mode::Public, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, false, Mode::Private, Mode::Constant, Mode::Private, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, false, Mode::Private, Mode::Public, Mode::Constant, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, false, Mode::Private, Mode::Public, Mode::Public, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, false, Mode::Private, Mode::Public, Mode::Private, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, false, Mode::Private, Mode::Private, Mode::Constant, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, false, Mode::Private, Mode::Private, Mode::Public, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, false, Mode::Private, Mode::Private, Mode::Private, Some((64, 0, 0, 0)));

        // Boolean(Private, true)
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, true, Mode::Private, Mode::Constant, Mode::Constant, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, true, Mode::Private, Mode::Constant, Mode::Public, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, true, Mode::Private, Mode::Constant, Mode::Private, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, true, Mode::Private, Mode::Public, Mode::Constant, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, true, Mode::Private, Mode::Public, Mode::Public, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, true, Mode::Private, Mode::Public, Mode::Private, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, true, Mode::Private, Mode::Private, Mode::Constant, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, true, Mode::Private, Mode::Private, Mode::Public, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, true, Mode::Private, Mode::Private, Mode::Private, Some((64, 0, 0, 0)));
    }

    #[test]
    #[rustfmt::skip]
    fn test_i128_ternary_all_modes() {
        // Boolean(Constant, false)
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, false, Mode::Constant, Mode::Constant, Mode::Constant, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, false, Mode::Constant, Mode::Constant, Mode::Public, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, false, Mode::Constant, Mode::Constant, Mode::Private, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, false, Mode::Constant, Mode::Public, Mode::Constant, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, false, Mode::Constant, Mode::Public, Mode::Public, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, false, Mode::Constant, Mode::Public, Mode::Private, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, false, Mode::Constant, Mode::Private, Mode::Constant, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, false, Mode::Constant, Mode::Private, Mode::Public, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, false, Mode::Constant, Mode::Private, Mode::Private, Some((128, 0, 0, 0)));

        // Boolean(Constant, true)
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, true, Mode::Constant, Mode::Constant, Mode::Constant, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, true, Mode::Constant, Mode::Constant, Mode::Public, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, true, Mode::Constant, Mode::Constant, Mode::Private, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, true, Mode::Constant, Mode::Public, Mode::Constant, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, true, Mode::Constant, Mode::Public, Mode::Public, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, true, Mode::Constant, Mode::Public, Mode::Private, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, true, Mode::Constant, Mode::Private, Mode::Constant, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, true, Mode::Constant, Mode::Private, Mode::Public, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, true, Mode::Constant, Mode::Private, Mode::Private, Some((128, 0, 0, 0)));

        // Boolean(Public, false)
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, false, Mode::Public, Mode::Constant, Mode::Constant, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, false, Mode::Public, Mode::Constant, Mode::Public, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, false, Mode::Public, Mode::Constant, Mode::Private, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, false, Mode::Public, Mode::Public, Mode::Constant, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, false, Mode::Public, Mode::Public, Mode::Public, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, false, Mode::Public, Mode::Public, Mode::Private, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, false, Mode::Public, Mode::Private, Mode::Constant, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, false, Mode::Public, Mode::Private, Mode::Public, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, false, Mode::Public, Mode::Private, Mode::Private, Some((128, 0, 0, 0)));

        // Boolean(Public, true)
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, true, Mode::Public, Mode::Constant, Mode::Constant, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, true, Mode::Public, Mode::Constant, Mode::Public, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, true, Mode::Public, Mode::Constant, Mode::Private, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, true, Mode::Public, Mode::Public, Mode::Constant, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, true, Mode::Public, Mode::Public, Mode::Public, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, true, Mode::Public, Mode::Public, Mode::Private, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, true, Mode::Public, Mode::Private, Mode::Constant, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, true, Mode::Public, Mode::Private, Mode::Public, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, true, Mode::Public, Mode::Private, Mode::Private, Some((128, 0, 0, 0)));

        // Boolean(Private, false)
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, false, Mode::Private, Mode::Constant, Mode::Constant, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, false, Mode::Private, Mode::Constant, Mode::Public, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, false, Mode::Private, Mode::Constant, Mode::Private, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, false, Mode::Private, Mode::Public, Mode::Constant, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, false, Mode::Private, Mode::Public, Mode::Public, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, false, Mode::Private, Mode::Public, Mode::Private, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, false, Mode::Private, Mode::Private, Mode::Constant, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, false, Mode::Private, Mode::Private, Mode::Public, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, false, Mode::Private, Mode::Private, Mode::Private, Some((128, 0, 0, 0)));

        // Boolean(Private, true)
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, true, Mode::Private, Mode::Constant, Mode::Constant, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, true, Mode::Private, Mode::Constant, Mode::Public, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, true, Mode::Private, Mode::Constant, Mode::Private, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, true, Mode::Private, Mode::Public, Mode::Constant, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, true, Mode::Private, Mode::Public, Mode::Public, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, true, Mode::Private, Mode::Public, Mode::Private, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, true, Mode::Private, Mode::Private, Mode::Constant, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, true, Mode::Private, Mode::Private, Mode::Public, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, true, Mode::Private, Mode::Private, Mode::Private, Some((128, 0, 0, 0)));
    }
}
