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
use crate::{BaseField, One, RippleCarryAdder, Zero};
use num_traits::WrappingAdd;
use snarkvm_fields::PrimeField;
use std::num::Wrapping;

impl<E: Environment, U: PrimitiveUnsignedInteger, const SIZE: usize> Add<Self> for Unsigned<E, U, SIZE> {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        self + &other
    }
}

// TODO (@pranav) Do we need to optimize the number of contraints generated?
//  This has the same implementation as signed addition? Can we dedup?
impl<E: Environment, U: PrimitiveUnsignedInteger, const SIZE: usize> Add<&Self> for Unsigned<E, U, SIZE> {
    type Output = Self;

    fn add(self, other: &Self) -> Self::Output {
        // Determine the variable mode.
        let mode = match self.is_constant() && other.is_constant() {
            true => Mode::Constant,
            false => Mode::Private,
        };

        // Directly compute the sum, check for overflow.
        let value = self.eject_value().wrapping_add(&other.eject_value());

        // If the resulting value is a constant, return it directly.
        if mode.is_constant() {
            return Unsigned::new(mode, value);
        }

        let mut bits = self.bits_le.add_bits(&other.bits_le);
        let _carry = bits.pop();

        assert_eq!(bits.len(), SIZE);

        for i in 0..SIZE {
            let mask = U::one() << i;
            let value_bit = Boolean::<E>::new(mode, value & mask == mask);
            value_bit.is_eq(&bits[i]);
        }

        Self::from_bits(bits)
    }
}

impl<E: Environment, U: PrimitiveUnsignedInteger, const SIZE: usize> Add<Unsigned<E, U, SIZE>>
    for &Unsigned<E, U, SIZE>
{
    type Output = Unsigned<E, U, SIZE>;

    fn add(self, other: Unsigned<E, U, SIZE>) -> Self::Output {
        (*self).clone() + other
    }
}

impl<E: Environment, U: PrimitiveUnsignedInteger, const SIZE: usize> Add<&Unsigned<E, U, SIZE>>
    for &Unsigned<E, U, SIZE>
{
    type Output = Unsigned<E, U, SIZE>;

    fn add(self, other: &Unsigned<E, U, SIZE>) -> Self::Output {
        (*self).clone() + other
    }
}

impl<E: Environment, U: PrimitiveUnsignedInteger, const SIZE: usize> AddAssign<Self> for Unsigned<E, U, SIZE> {
    fn add_assign(&mut self, other: Self) {
        *self += &other;
    }
}

impl<E: Environment, U: PrimitiveUnsignedInteger, const SIZE: usize> AddAssign<&Self> for Unsigned<E, U, SIZE> {
    fn add_assign(&mut self, other: &Self) {
        *self = self.clone() + other;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{unsigned::test_utilities::check_operation, Circuit};
    use snarkvm_utilities::UniformRand;

    use rand::{
        distributions::{Distribution, Standard},
        thread_rng,
    };
    use std::num::Wrapping;

    const ITERATIONS: usize = 100;

    fn run_test<E: Environment, U: PrimitiveUnsignedInteger, const SIZE: usize>(
        iterations: usize,
        mode_a: Mode,
        mode_b: Mode,
        circuit_properties: Option<(usize, usize, usize, usize)>,
    ) where
        Standard: Distribution<U>,
    {
        for i in 0..iterations {
            let first: U = UniformRand::rand(&mut thread_rng());
            let second: U = UniformRand::rand(&mut thread_rng());

            let expected = first.wrapping_add(&second);
            let a = Unsigned::<E, U, SIZE>::new(mode_a, first);
            let b = Unsigned::<E, U, SIZE>::new(mode_b, second);

            let name = format!("Add: a + b {}", i);
            let compute_candidate = || &a + &b;
            check_operation::<E, U, SIZE>(&name, expected, &compute_candidate, circuit_properties);

            let name = format!("AddAssign: a += b {}", i);
            let compute_candidate = || {
                let mut candidate = (&a).clone();
                candidate += &b;
                candidate
            };
            check_operation::<E, U, SIZE>(&name, expected, &compute_candidate, circuit_properties);
        }
    }

    #[test]
    fn test_u8_add_all_modes() {
        run_test::<Circuit, u8, 8>(ITERATIONS, Mode::Constant, Mode::Constant, Some((8, 0, 0, 0)));
        run_test::<Circuit, u8, 8>(ITERATIONS, Mode::Constant, Mode::Public, None);
        run_test::<Circuit, u8, 8>(ITERATIONS, Mode::Constant, Mode::Private, None);
        run_test::<Circuit, u8, 8>(ITERATIONS, Mode::Public, Mode::Constant, None);
        run_test::<Circuit, u8, 8>(ITERATIONS, Mode::Public, Mode::Public, Some((8, 0, 0, 0)));
        run_test::<Circuit, u8, 8>(ITERATIONS, Mode::Public, Mode::Private, Some((8, 0, 0, 0)));
        run_test::<Circuit, u8, 8>(ITERATIONS, Mode::Private, Mode::Constant, None);
        run_test::<Circuit, u8, 8>(ITERATIONS, Mode::Private, Mode::Public, Some((8, 0, 0, 0)));
        run_test::<Circuit, u8, 8>(ITERATIONS, Mode::Private, Mode::Private, Some((8, 0, 0, 0)));
    }

    #[test]
    fn test_u16_add_all_modes() {
        run_test::<Circuit, u16, 16>(ITERATIONS, Mode::Constant, Mode::Constant, Some((16, 0, 0, 0)));
        run_test::<Circuit, u16, 16>(ITERATIONS, Mode::Constant, Mode::Public, None);
        run_test::<Circuit, u16, 16>(ITERATIONS, Mode::Constant, Mode::Private, None);
        run_test::<Circuit, u16, 16>(ITERATIONS, Mode::Public, Mode::Constant, None);
        run_test::<Circuit, u16, 16>(ITERATIONS, Mode::Public, Mode::Public, Some((16, 0, 0, 0)));
        run_test::<Circuit, u16, 16>(ITERATIONS, Mode::Public, Mode::Private, Some((16, 0, 0, 0)));
        run_test::<Circuit, u16, 16>(ITERATIONS, Mode::Private, Mode::Constant, None);
        run_test::<Circuit, u16, 16>(ITERATIONS, Mode::Private, Mode::Public, Some((16, 0, 0, 0)));
        run_test::<Circuit, u16, 16>(ITERATIONS, Mode::Private, Mode::Private, Some((16, 0, 0, 0)));
    }

    #[test]
    fn test_u32_add_all_modes() {
        run_test::<Circuit, u32, 32>(ITERATIONS, Mode::Constant, Mode::Constant, Some((32, 0, 0, 0)));
        run_test::<Circuit, u32, 32>(ITERATIONS, Mode::Constant, Mode::Public, None);
        run_test::<Circuit, u32, 32>(ITERATIONS, Mode::Constant, Mode::Private, None);
        run_test::<Circuit, u32, 32>(ITERATIONS, Mode::Public, Mode::Constant, None);
        run_test::<Circuit, u32, 32>(ITERATIONS, Mode::Public, Mode::Public, Some((32, 0, 0, 0)));
        run_test::<Circuit, u32, 32>(ITERATIONS, Mode::Public, Mode::Private, Some((32, 0, 0, 0)));
        run_test::<Circuit, u32, 32>(ITERATIONS, Mode::Private, Mode::Constant, None);
        run_test::<Circuit, u32, 32>(ITERATIONS, Mode::Private, Mode::Public, Some((32, 0, 0, 0)));
        run_test::<Circuit, u32, 32>(ITERATIONS, Mode::Private, Mode::Private, Some((32, 0, 0, 0)));
    }

    #[test]
    fn test_u64_add_all_modes() {
        run_test::<Circuit, u64, 64>(ITERATIONS, Mode::Constant, Mode::Constant, Some((64, 0, 0, 0)));
        run_test::<Circuit, u64, 64>(ITERATIONS, Mode::Constant, Mode::Public, None);
        run_test::<Circuit, u64, 64>(ITERATIONS, Mode::Constant, Mode::Private, None);
        run_test::<Circuit, u64, 64>(ITERATIONS, Mode::Public, Mode::Constant, None);
        run_test::<Circuit, u64, 64>(ITERATIONS, Mode::Public, Mode::Public, Some((64, 0, 0, 0)));
        run_test::<Circuit, u64, 64>(ITERATIONS, Mode::Public, Mode::Private, Some((64, 0, 0, 0)));
        run_test::<Circuit, u64, 64>(ITERATIONS, Mode::Private, Mode::Constant, None);
        run_test::<Circuit, u64, 64>(ITERATIONS, Mode::Private, Mode::Public, Some((64, 0, 0, 0)));
        run_test::<Circuit, u64, 64>(ITERATIONS, Mode::Private, Mode::Private, Some((64, 0, 0, 0)));
    }

    #[test]
    fn test_u128_add_all_modes() {
        run_test::<Circuit, u128, 128>(ITERATIONS, Mode::Constant, Mode::Constant, Some((128, 0, 0, 0)));
        run_test::<Circuit, u128, 128>(ITERATIONS, Mode::Constant, Mode::Public, None);
        run_test::<Circuit, u128, 128>(ITERATIONS, Mode::Constant, Mode::Private, None);
        run_test::<Circuit, u128, 128>(ITERATIONS, Mode::Public, Mode::Constant, None);
        run_test::<Circuit, u128, 128>(ITERATIONS, Mode::Public, Mode::Public, Some((128, 0, 0, 0)));
        run_test::<Circuit, u128, 128>(ITERATIONS, Mode::Public, Mode::Private, Some((128, 0, 0, 0)));
        run_test::<Circuit, u128, 128>(ITERATIONS, Mode::Private, Mode::Constant, None);
        run_test::<Circuit, u128, 128>(ITERATIONS, Mode::Private, Mode::Public, Some((128, 0, 0, 0)));
        run_test::<Circuit, u128, 128>(ITERATIONS, Mode::Private, Mode::Private, Some((128, 0, 0, 0)));
    }
}
