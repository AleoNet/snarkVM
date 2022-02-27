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
use crate::unsigned::Unsigned;

impl<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize> Div<Self>
    for Signed<E, I, U, SIZE>
{
    type Output = Self;

    fn div(self, other: Self) -> Self::Output {
        self / &other
    }
}

impl<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize> Div<&Self>
    for Signed<E, I, U, SIZE>
{
    type Output = Self;

    // TODO (@pranav) Would a more efficient division algorithm in a traditional sense
    //   yield a more efficient implementation in a SNARK context?
    fn div(self, other: &Self) -> Self::Output {
        // Determine the variable mode.
        let mode = match self.is_constant() && other.is_constant() {
            true => Mode::Constant,
            false => Mode::Private,
        };

        // Directly compute the quotient, wrapping if neccessary. Check for division by zero.
        let self_value = self.eject_value();
        let other_value = other.eject_value();
        if other_value == I::zero() {
            E::halt("Division by zero.")
        }
        let value = self_value.wrapping_div(&other_value);

        if mode.is_constant() {
            return Signed::new(mode, value);
        }

        // N / D pseudocode:
        //
        // if D = 0 then error(DivisionByZeroException) end
        //
        // positive = msb(N) == msb(D) -- if msb's equal, return positive result
        //
        // Q := 0                  -- Initialize quotient and remainder to zero
        // R := 0
        //
        // for i := n − 1 .. 0 do  -- Where n is number of bits in N
        //   R := R << 1           -- Left-shift R by 1 bit
        //   R(0) := N(i)          -- Set the least-significant bit of R equal to bit i of the numerator
        //   if R ≥ D then
        //     R := R − D
        //     Q(i) := 1
        //   end
        // end
        //
        // if positive then           -- positive result
        //    Q
        // else
        //    !Q                      -- negative result

        // If self is MIN and other is -1, then return MIN
        let self_is_min = self.is_eq(&Signed::new(Mode::Constant, I::min_value()));
        let other_is_minus_one = other.is_eq(&Signed::new(Mode::Constant, I::zero() - I::one())); //TODO (@pranav) wrapping sub?
        let wrapping_condition = self_is_min.and(&other_is_minus_one);

        // Division by zero is already checked above.
        let a_msb = self.bits_le.last().unwrap();
        let other_msb = other.bits_le.last().unwrap();
        let positive = a_msb.is_eq(&other_msb);

        let self_absolute_value = Signed::ternary(a_msb, &self.clone().neg(), &self.clone());
        let other_absolute_value = Signed::ternary(other_msb, &other.clone().neg(), &other.clone());

        let unsigned_quotient = Unsigned::<E, U, SIZE>::from_bits(self_absolute_value.bits_le)
            / Unsigned::<E, U, SIZE>::from_bits(other_absolute_value.bits_le);

        let quotient = Signed::from_bits(unsigned_quotient.bits_le);
        let signed_quotient = Signed::ternary(&positive, &quotient, &(&quotient).neg());
        let result = Signed::ternary(
            &wrapping_condition,
            &Signed::new(mode, I::min_value()),
            &signed_quotient,
        );

        // Check that the computed result matches the expected one.
        for i in 0..SIZE {
            let mask = I::one() << i;
            let value_bit = Boolean::<E>::new(mode, value & mask == mask);
            value_bit.is_eq(&result.bits_le[i]);
        }
        result
    }
}

impl<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize>
    Div<Signed<E, I, U, SIZE>> for &Signed<E, I, U, SIZE>
{
    type Output = Signed<E, I, U, SIZE>;

    fn div(self, other: Signed<E, I, U, SIZE>) -> Self::Output {
        (*self).clone() / other
    }
}

impl<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize>
    Div<&Signed<E, I, U, SIZE>> for &Signed<E, I, U, SIZE>
{
    type Output = Signed<E, I, U, SIZE>;

    fn div(self, other: &Signed<E, I, U, SIZE>) -> Self::Output {
        (*self).clone() / other
    }
}

impl<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize> DivAssign<Self>
    for Signed<E, I, U, SIZE>
{
    fn div_assign(&mut self, other: Self) {
        *self /= &other;
    }
}

impl<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize> DivAssign<&Self>
    for Signed<E, I, U, SIZE>
{
    fn div_assign(&mut self, other: &Self) {
        *self = self.clone() / other;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{signed::test_utilities::check_operation, Circuit};
    use snarkvm_utilities::UniformRand;

    use rand::{
        distributions::{Distribution, Standard},
        thread_rng,
    };

    const ITERATIONS: usize = 1;

    fn test_div<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize>(
        iterations: usize,
        mode_a: Mode,
        mode_b: Mode,
        circuit_properties: Option<(usize, usize, usize, usize)>,
    ) where
        Standard: Distribution<I>,
    {
        for i in 0..iterations {
            let first: I = UniformRand::rand(&mut thread_rng());
            let second: I = UniformRand::rand(&mut thread_rng());

            let expected = first.wrapping_div(&second);

            let name = format!("Div: a / b {}", i);
            let compute_candidate = || {
                let a = Signed::<E, I, U, SIZE>::new(mode_a, first);
                let b = Signed::<E, I, U, SIZE>::new(mode_b, second);
                a / b
            };
            check_operation::<E, I, U, SIZE>(&name, expected, &compute_candidate, circuit_properties);
        }
    }

    fn test_div_assign<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize>(
        iterations: usize,
        mode_a: Mode,
        mode_b: Mode,
        circuit_properties: Option<(usize, usize, usize, usize)>,
    ) where
        Standard: Distribution<I>,
    {
        for i in 0..iterations {
            let first: I = UniformRand::rand(&mut thread_rng());
            let second: I = UniformRand::rand(&mut thread_rng());

            let expected = first.wrapping_div(&second);

            let name = format!("DivAssign: a /= b {}", i);
            let compute_candidate = || {
                let mut a = Signed::<E, I, U, SIZE>::new(mode_a, first);
                let b = Signed::<E, I, U, SIZE>::new(mode_b, second);
                a /= b;
                a
            };
            check_operation::<E, I, U, SIZE>(&name, expected, &compute_candidate, circuit_properties);
        }
    }

    #[test]
    fn test_i8_div_constant_constant() {
        test_div::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Constant, Mode::Constant, Some((24, 0, 0, 0)));
        test_div_assign::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Constant, Mode::Constant, Some((24, 0, 0, 0)));
    }

    #[test]
    fn test_i8_div_constant_public() {
        test_div::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Constant, Mode::Public, None);
        test_div_assign::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Constant, Mode::Public, None);
    }

    #[test]
    fn test_i8_div_constant_private() {
        test_div::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Constant, Mode::Private, None);
        test_div_assign::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Constant, Mode::Private, None);
    }

    #[test]
    fn test_i8_div_public_constant() {
        test_div::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Public, Mode::Constant, None);
        test_div_assign::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Public, Mode::Constant, None);
    }

    #[test]
    fn test_i8_div_public_public() {
        test_div::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Public, Mode::Public, Some((221, 16, 2066, 3836)));
        test_div_assign::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Public, Mode::Public, Some((221, 16, 2066, 3836)));
    }

    #[test]
    fn test_i8_div_public_private() {
        test_div::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Public, Mode::Private, Some((221, 8, 2074, 3836)));
        test_div_assign::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Public, Mode::Private, Some((221, 8, 2074, 3836)));
    }

    #[test]
    fn test_i8_div_private_constant() {
        test_div::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Private, Mode::Constant, None);
        test_div_assign::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Private, Mode::Constant, None);
    }

    #[test]
    fn test_i8_div_private_public() {
        test_div::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Private, Mode::Public, Some((221, 8, 2074, 3836)));
        test_div_assign::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Private, Mode::Public, Some((221, 8, 2074, 3836)));
    }

    #[test]
    fn test_i8_div_private_private() {
        test_div::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Private, Mode::Private, Some((221, 0, 2082, 3836)));
        test_div_assign::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Private, Mode::Private, Some((221, 0, 2082, 3836)));
    }

    // Tests for i16

    #[test]
    fn test_i16_div_constant_constant() {
        test_div::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Constant, Mode::Constant, Some((48, 0, 0, 0)));
        test_div_assign::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Constant, Mode::Constant, Some((48, 0, 0, 0)));
    }

    #[test]
    fn test_i16_div_constant_public() {
        test_div::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Constant, Mode::Public, None);
        test_div_assign::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Constant, Mode::Public, None);
    }

    #[test]
    fn test_i16_div_constant_private() {
        test_div::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Constant, Mode::Private, None);
        test_div_assign::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Constant, Mode::Private, None);
    }

    #[test]
    fn test_i16_div_public_constant() {
        test_div::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Public, Mode::Constant, None);
        test_div_assign::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Public, Mode::Constant, None);
    }

    #[test]
    fn test_i16_div_public_public() {
        test_div::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Public, Mode::Public, Some((693, 32, 8106, 15108)));
        test_div_assign::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Public, Mode::Public, Some((693, 32, 8106, 15108)));
    }

    #[test]
    fn test_i16_div_public_private() {
        test_div::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Public, Mode::Private, Some((693, 16, 8122, 15108)));
        test_div_assign::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Public, Mode::Private, Some((693, 16, 8122, 15108)));
    }

    #[test]
    fn test_i16_div_private_constant() {
        test_div::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Private, Mode::Constant, None);
        test_div_assign::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Private, Mode::Constant, None);
    }

    #[test]
    fn test_i16_div_private_public() {
        test_div::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Private, Mode::Public, Some((693, 16, 8122, 15108)));
        test_div_assign::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Private, Mode::Public, Some((693, 16, 8122, 15108)));
    }

    #[test]
    fn test_i16_div_private_private() {
        test_div::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Private, Mode::Private, Some((693, 0, 8138, 15108)));
        test_div_assign::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Private, Mode::Private, Some((693, 0, 8138, 15108)));
    }

    // Tests for i32

    #[test]
    fn test_i32_div_constant_constant() {
        test_div::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Constant, Mode::Constant, Some((96, 0, 0, 0)));
        test_div_assign::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Constant, Mode::Constant, Some((96, 0, 0, 0)));
    }

    #[test]
    fn test_i32_div_constant_public() {
        test_div::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Constant, Mode::Public, None);
        test_div_assign::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Constant, Mode::Public, None);
    }

    #[test]
    fn test_i32_div_constant_private() {
        test_div::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Constant, Mode::Private, None);
        test_div_assign::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Constant, Mode::Private, None);
    }

    #[test]
    fn test_i32_div_public_constant() {
        test_div::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Public, Mode::Constant, None);
        test_div_assign::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Public, Mode::Constant, None);
    }

    #[test]
    fn test_i32_div_public_public() {
        test_div::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Public, Mode::Public, Some((2405, 64, 32090, 59924)));
        test_div_assign::<Circuit, i32, u32, 32>(
            ITERATIONS,
            Mode::Public,
            Mode::Public,
            Some((2405, 64, 32090, 59924)),
        );
    }

    #[test]
    fn test_i32_div_public_private() {
        test_div::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Public, Mode::Private, Some((2405, 32, 32122, 59924)));
        test_div_assign::<Circuit, i32, u32, 32>(
            ITERATIONS,
            Mode::Public,
            Mode::Private,
            Some((2405, 32, 32122, 59924)),
        );
    }

    #[test]
    fn test_i32_div_private_constant() {
        test_div::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Private, Mode::Constant, None);
        test_div_assign::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Private, Mode::Constant, None);
    }

    #[test]
    fn test_i32_div_private_public() {
        test_div::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Private, Mode::Public, Some((2405, 32, 32122, 59924)));
        test_div_assign::<Circuit, i32, u32, 32>(
            ITERATIONS,
            Mode::Private,
            Mode::Public,
            Some((2405, 32, 32122, 59924)),
        );
    }

    #[test]
    fn test_i32_div_private_private() {
        test_div::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Private, Mode::Private, Some((2405, 0, 32154, 59924)));
        test_div_assign::<Circuit, i32, u32, 32>(
            ITERATIONS,
            Mode::Private,
            Mode::Private,
            Some((2405, 0, 32154, 59924)),
        );
    }

    // Tests for i64

    #[test]
    fn test_i64_div_constant_constant() {
        test_div::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Constant, Mode::Constant, Some((192, 0, 0, 0)));
        test_div_assign::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Constant, Mode::Constant, Some((192, 0, 0, 0)));
    }

    #[test]
    fn test_i64_div_constant_public() {
        test_div::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Constant, Mode::Public, None);
        test_div_assign::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Constant, Mode::Public, None);
    }

    #[test]
    fn test_i64_div_constant_private() {
        test_div::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Constant, Mode::Private, None);
        test_div_assign::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Constant, Mode::Private, None);
    }

    #[test]
    fn test_i64_div_public_constant() {
        test_div::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Public, Mode::Constant, None);
        test_div_assign::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Public, Mode::Constant, None);
    }

    #[test]
    fn test_i64_div_public_public() {
        test_div::<Circuit, i64, u64, 64>(
            ITERATIONS,
            Mode::Public,
            Mode::Public,
            Some((8901, 128, 127674, 238644)),
        );
        test_div_assign::<Circuit, i64, u64, 64>(
            ITERATIONS,
            Mode::Public,
            Mode::Public,
            Some((8901, 128, 127674, 238644)),
        );
    }

    #[test]
    fn test_i64_div_public_private() {
        test_div::<Circuit, i64, u64, 64>(
            ITERATIONS,
            Mode::Public,
            Mode::Private,
            Some((8901, 64, 127738, 238644)),
        );
        test_div_assign::<Circuit, i64, u64, 64>(
            ITERATIONS,
            Mode::Public,
            Mode::Private,
            Some((8901, 64, 127738, 238644)),
        );
    }

    #[test]
    fn test_i64_div_private_constant() {
        test_div::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Private, Mode::Constant, None);
        test_div_assign::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Private, Mode::Constant, None);
    }

    #[test]
    fn test_i64_div_private_public() {
        test_div::<Circuit, i64, u64, 64>(
            ITERATIONS,
            Mode::Private,
            Mode::Public,
            Some((8901, 64, 127738, 238644)),
        );
        test_div_assign::<Circuit, i64, u64, 64>(
            ITERATIONS,
            Mode::Private,
            Mode::Public,
            Some((8901, 64, 127738, 238644)),
        );
    }

    #[test]
    fn test_i64_div_private_private() {
        test_div::<Circuit, i64, u64, 64>(
            ITERATIONS,
            Mode::Private,
            Mode::Private,
            Some((8901, 0, 127802, 238644)),
        );
        test_div_assign::<Circuit, i64, u64, 64>(
            ITERATIONS,
            Mode::Private,
            Mode::Private,
            Some((8901, 0, 127802, 238644)),
        );
    }

    // Tests for i128

    #[test]
    fn test_i128_div_constant_constant() {
        test_div::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Constant, Mode::Constant, Some((384, 0, 0, 0)));
        test_div_assign::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Constant, Mode::Constant, Some((384, 0, 0, 0)));
    }

    #[test]
    fn test_i128_div_constant_public() {
        test_div::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Constant, Mode::Public, None);
        test_div_assign::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Constant, Mode::Public, None);
    }

    #[test]
    fn test_i128_div_constant_private() {
        test_div::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Constant, Mode::Private, None);
        test_div_assign::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Constant, Mode::Private, None);
    }

    #[test]
    fn test_i128_div_public_constant() {
        test_div::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Public, Mode::Constant, None);
        test_div_assign::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Public, Mode::Constant, None);
    }

    #[test]
    fn test_i128_div_public_public() {
        test_div::<Circuit, i128, u128, 128>(
            ITERATIONS,
            Mode::Public,
            Mode::Public,
            Some((34181, 256, 509306, 952436)),
        );
        test_div_assign::<Circuit, i128, u128, 128>(
            ITERATIONS,
            Mode::Public,
            Mode::Public,
            Some((34181, 256, 509306, 952436)),
        );
    }

    #[test]
    fn test_i128_div_public_private() {
        test_div::<Circuit, i128, u128, 128>(
            ITERATIONS,
            Mode::Public,
            Mode::Private,
            Some((34181, 128, 509434, 952436)),
        );
        test_div_assign::<Circuit, i128, u128, 128>(
            ITERATIONS,
            Mode::Public,
            Mode::Private,
            Some((34181, 128, 509434, 952436)),
        );
    }

    #[test]
    fn test_i128_div_private_constant() {
        test_div::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Private, Mode::Constant, None);
        test_div_assign::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Private, Mode::Constant, None);
    }

    #[test]
    fn test_i128_div_private_public() {
        test_div::<Circuit, i128, u128, 128>(
            ITERATIONS,
            Mode::Private,
            Mode::Public,
            Some((34181, 128, 509434, 952436)),
        );
        test_div_assign::<Circuit, i128, u128, 128>(
            ITERATIONS,
            Mode::Private,
            Mode::Public,
            Some((34181, 128, 509434, 952436)),
        );
    }

    #[test]
    fn test_i128_div_private_private() {
        test_div::<Circuit, i128, u128, 128>(
            ITERATIONS,
            Mode::Private,
            Mode::Private,
            Some((34181, 0, 509562, 952436)),
        );
        test_div_assign::<Circuit, i128, u128, 128>(
            ITERATIONS,
            Mode::Private,
            Mode::Private,
            Some((34181, 0, 509562, 952436)),
        );
    }
}
