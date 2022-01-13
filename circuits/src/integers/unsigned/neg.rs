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
use crate::RippleCarryAdder;

impl<E: Environment, U: PrimitiveUnsignedInteger, const SIZE: usize> Neg for Unsigned<E, U, SIZE> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        let value = self.eject_value().wrapping_neg();

        if self.is_constant() {
            return Unsigned::new(Mode::Constant, value);
        }

        let flipped = Unsigned::from_bits(self.bits_le.iter().map(|bit| !bit).collect());
        let mut one = Unsigned::new(Mode::Constant, U::one());
        let result = flipped.add(one);

        // TODO (@pranav) Is this check necessary? It does not seem to be done in the corresponding
        //   gadget implementation.
        // Check that the computed result is correct
        for i in 0..SIZE {
            let mask = U::one() << i;
            let value_bit = Boolean::<E>::new(Mode::Private, value & mask == mask);
            value_bit.is_eq(&result.bits_le[i]);
        }

        result
    }
}

impl<E: Environment, U: PrimitiveUnsignedInteger, const SIZE: usize> Neg for &Unsigned<E, U, SIZE> {
    type Output = Unsigned<E, U, SIZE>;

    fn neg(self) -> Self::Output {
        -(self.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;

    use crate::integers::unsigned::test_utilities::check_operation;
    use rand::{
        distributions::{Distribution, Standard},
        thread_rng,
    };

    const ITERATIONS: usize = 1000;

    fn run_test<E: Environment, U: PrimitiveUnsignedInteger, const SIZE: usize>(
        iterations: usize,
        mode: Mode,
        circuit_properties: Option<(usize, usize, usize, usize)>,
    ) where
        Standard: Distribution<U>,
    {
        for i in 0..iterations {
            let first: U = UniformRand::rand(&mut thread_rng());

            let expected = first.wrapping_neg();
            let a = Unsigned::<E, U, SIZE>::new(mode, first);

            let name = format!("Neg: -a {}", i);
            let compute_candidate = || {
                let a = Unsigned::<E, U, SIZE>::new(mode, first);
                -a
            };
            check_operation::<E, U, SIZE>(&name, expected, &compute_candidate, circuit_properties);
        }
    }

    #[test]
    fn test_i8_neg_all_modes() {
        run_test::<Circuit, u8, 8>(ITERATIONS, Mode::Constant, Some((8, 0, 0, 0)));
        run_test::<Circuit, u8, 8>(ITERATIONS, Mode::Public, Some((8, 0, 0, 0)));
        run_test::<Circuit, u8, 8>(ITERATIONS, Mode::Private, Some((8, 0, 0, 0)));
    }

    #[test]
    fn test_i16_neg_all_modes() {
        run_test::<Circuit, u16, 16>(ITERATIONS, Mode::Constant, Some((16, 0, 0, 0)));
        run_test::<Circuit, u16, 16>(ITERATIONS, Mode::Public, Some((16, 0, 0, 0)));
        run_test::<Circuit, u16, 16>(ITERATIONS, Mode::Private, Some((16, 0, 0, 0)));
    }

    #[test]
    fn test_i32_neg_all_modes() {
        run_test::<Circuit, u32, 32>(ITERATIONS, Mode::Constant, Some((32, 0, 0, 0)));
        run_test::<Circuit, u32, 32>(ITERATIONS, Mode::Public, Some((32, 0, 0, 0)));
        run_test::<Circuit, u32, 32>(ITERATIONS, Mode::Private, Some((32, 0, 0, 0)));
    }

    #[test]
    fn test_i64_neg_all_modes() {
        run_test::<Circuit, u64, 64>(ITERATIONS, Mode::Constant, Some((64, 0, 0, 0)));
        run_test::<Circuit, u64, 64>(ITERATIONS, Mode::Public, Some((64, 0, 0, 0)));
        run_test::<Circuit, u64, 64>(ITERATIONS, Mode::Private, Some((64, 0, 0, 0)));
    }

    #[test]
    fn test_i128_neg_all_modes() {
        run_test::<Circuit, u128, 128>(ITERATIONS, Mode::Constant, Some((128, 0, 0, 0)));
        run_test::<Circuit, u128, 128>(ITERATIONS, Mode::Public, Some((128, 0, 0, 0)));
        run_test::<Circuit, u128, 128>(ITERATIONS, Mode::Private, Some((128, 0, 0, 0)));
    }
}
