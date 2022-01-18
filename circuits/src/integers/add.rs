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
use crate::helpers::AddWithCarry;

use itertools::Itertools;

impl<E: Environment, I: IntegerType, const BITS: usize> Add<Integer<E, I, BITS>> for Integer<E, I, BITS> {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        self + &other
    }
}

impl<E: Environment, I: IntegerType, const BITS: usize> Add<Integer<E, I, BITS>> for &Integer<E, I, BITS> {
    type Output = Integer<E, I, BITS>;

    fn add(self, other: Integer<E, I, BITS>) -> Self::Output {
        self + &other
    }
}

impl<E: Environment, I: IntegerType, const BITS: usize> Add<&Integer<E, I, BITS>> for Integer<E, I, BITS> {
    type Output = Self;

    fn add(self, other: &Self) -> Self::Output {
        &self + other
    }
}

impl<E: Environment, I: IntegerType, const BITS: usize> Add<&Integer<E, I, BITS>> for &Integer<E, I, BITS> {
    type Output = Integer<E, I, BITS>;

    fn add(self, other: &Integer<E, I, BITS>) -> Self::Output {
        let mut output = self.clone();
        output += other;
        output
    }
}

impl<E: Environment, I: IntegerType, const BITS: usize> AddAssign<Integer<E, I, BITS>> for Integer<E, I, BITS> {
    fn add_assign(&mut self, other: Integer<E, I, BITS>) {
        *self += &other;
    }
}

impl<E: Environment, I: IntegerType, const BITS: usize> AddAssign<&Integer<E, I, BITS>> for Integer<E, I, BITS> {
    fn add_assign(&mut self, other: &Integer<E, I, BITS>) {
        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the sum and return the new constant.
            *self = Integer::new(Mode::Constant, self.eject_value().wrapping_add(&other.eject_value()));
        } else {
            let mut bits_le = Vec::with_capacity(BITS);
            let mut carry = Boolean::new(Mode::Constant, false);

            // Perform a ripple-carry adder on the bits.
            for (a, b) in self.bits_le.iter().zip_eq(other.bits_le.iter()).take(BITS) {
                let (sum, next) = a.add_with_carry(b, &carry);
                carry = next;
                bits_le.push(sum);
            }

            // TODO (howardwu): Either a) enforce the carry bit is 0, or b) perform an overflow operation.

            // Stores the sum of `self` and `other` in `self`.
            *self = Self::from_bits(bits_le);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

    const ITERATIONS: usize = 100;

    fn check_add<I: IntegerType, IC: IntegerTrait<I>>(
        name: &str,
        expected: I,
        a: &IC,
        b: &IC,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, |scope| {
            let candidate = a.clone() + b.clone();
            assert_eq!(
                expected,
                candidate.eject_value(),
                "{} != {} := ({} + {})",
                expected,
                candidate.eject_value(),
                a.eject_value(),
                b.eject_value()
            );

            assert_eq!(num_constants, scope.num_constants_in_scope());
            assert_eq!(num_public, scope.num_public_in_scope());
            assert_eq!(num_private, scope.num_private_in_scope());
            assert_eq!(num_constraints, scope.num_constraints_in_scope());
            assert!(Circuit::is_satisfied());
        });
    }

    fn check_add_assign<I: IntegerType, IC: IntegerTrait<I>>(
        name: &str,
        expected: I,
        a: &IC,
        b: &IC,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, |scope| {
            let mut candidate = a.clone();
            candidate += b.clone();
            assert_eq!(
                expected,
                candidate.eject_value(),
                "{} != {} := ({} + {})",
                expected,
                candidate.eject_value(),
                a.eject_value(),
                b.eject_value()
            );

            assert_eq!(num_constants, scope.num_constants_in_scope());
            assert_eq!(num_public, scope.num_public_in_scope());
            assert_eq!(num_private, scope.num_private_in_scope());
            assert_eq!(num_constraints, scope.num_constraints_in_scope());
            assert!(Circuit::is_satisfied());
        });
    }

    #[test]
    fn test_u8_constant_plus_constant() {
        type I = u8;
        type IC = Integer<Circuit, I, { I::BITS as usize }>;

        for i in 0..ITERATIONS {
            let first: I = UniformRand::rand(&mut thread_rng());
            let second: I = UniformRand::rand(&mut thread_rng());
            let expected = first.wrapping_add(second);

            let a = IC::new(Mode::Constant, first);
            let b = IC::new(Mode::Constant, second);

            let name = format!("Add: a + b {}", i);
            check_add::<I, IC>(&name, expected, &a, &b, 8, 0, 0, 0);
            let name = format!("AddAssign: a += b {}", i);
            check_add_assign::<I, IC>(&name, expected, &a, &b, 8, 0, 0, 0);
        }
    }

    // #[test]
    // fn test_u8_constant_plus_public() {
    //     type I = u8;
    //     type IC = Integer<Circuit, I, { I::BITS as usize }>;
    //
    //     for i in 0..ITERATIONS {
    //         let first: I = UniformRand::rand(&mut thread_rng());
    //         let second: I = UniformRand::rand(&mut thread_rng());
    //         let expected = first.wrapping_add(second);
    //
    //         let a = IC::new(Mode::Constant, first);
    //         let b = IC::new(Mode::Public, second);
    //
    //         let name = format!("Add: a + b {}", i);
    //         check_add::<I, IC>(&name, expected, &a, &b, 1, 0, 1, 0);
    //         let name = format!("AddAssign: a += b {}", i);
    //         check_add_assign::<I, IC>(&name, expected, &a, &b, 8, 0, 16, 0);
    //     }
    // }

    // #[test]
    // fn test_u8_add_constant_private() {
    //     check_add::<Circuit, u8, 8>(Mode::Constant, Mode::Private, None);
    //     check_add_assign::<Circuit, u8, 8>(Mode::Constant, Mode::Private, None);
    // }
    //
    // #[test]
    // fn test_u8_add_public_constant() {
    //     check_add::<Circuit, u8, 8>(Mode::Public, Mode::Constant, None);
    //     check_add_assign::<Circuit, u8, 8>(Mode::Public, Mode::Constant, None);
    // }
    //
    // #[test]
    // fn test_u8_add_private_constant() {
    //     check_add::<Circuit, u8, 8>(Mode::Private, Mode::Constant, None);
    //     check_add_assign::<Circuit, u8, 8>(Mode::Private, Mode::Constant, None);
    // }
    //
    // #[test]
    // fn test_u8_add_public_public() {
    //     check_add::<Circuit, u8, 8>(Mode::Public, Mode::Public, 1, 16, 45, 106);
    //     check_add_assign::<Circuit, u8, 8>(Mode::Public, Mode::Public, 1, 16, 45, 106);
    // }
    //
    // #[test]
    // fn test_u8_add_public_private() {
    //     check_add::<Circuit, u8, 8>(Mode::Public, Mode::Private, 1, 8, 53, 106);
    //     check_add_assign::<Circuit, u8, 8>(Mode::Public, Mode::Private, 1, 8, 53, 106);
    // }
    //
    // #[test]
    // fn test_u8_add_private_public() {
    //     check_add::<Circuit, u8, 8>(Mode::Private, Mode::Public, 1, 8, 53, 106);
    //     check_add_assign::<Circuit, u8, 8>(Mode::Private, Mode::Public, 1, 8, 53, 106);
    // }

    #[test]
    fn test_u8_private_plus_private() {
        type I = u8;
        type IC = Integer<Circuit, I, { I::BITS as usize }>;

        for i in 0..ITERATIONS {
            let first: I = UniformRand::rand(&mut thread_rng());
            let second: I = UniformRand::rand(&mut thread_rng());
            let expected = first.wrapping_add(second);

            let a = IC::new(Mode::Private, first);
            let b = IC::new(Mode::Private, second);

            let name = format!("Add: a + b {}", i);
            check_add::<I, IC>(&name, expected, &a, &b, 1, 0, 37, 74);
            let name = format!("AddAssign: a += b {}", i);
            check_add_assign::<I, IC>(&name, expected, &a, &b, 1, 0, 37, 74);
        }
    }

    // // Tests for i16
    //
    // #[test]
    // fn test_u16_add_constant_constant() {
    //     check_add::<Circuit, u16, 16>(Mode::Constant, Mode::Constant, 48, 0, 0, 0);
    //     check_add_assign::<Circuit, u16, 16>(Mode::Constant, Mode::Constant, 48, 0, 0, 0);
    // }
    //
    // #[test]
    // fn test_u16_add_constant_public() {
    //     check_add::<Circuit, u16, 16>(Mode::Constant, Mode::Public, None);
    //     check_add_assign::<Circuit, u16, 16>(Mode::Constant, Mode::Public, None);
    // }
    //
    // #[test]
    // fn test_u16_add_constant_private() {
    //     check_add::<Circuit, u16, 16>(Mode::Constant, Mode::Private, None);
    //     check_add_assign::<Circuit, u16, 16>(Mode::Constant, Mode::Private, None);
    // }
    //
    // #[test]
    // fn test_u16_add_public_constant() {
    //     check_add::<Circuit, u16, 16>(Mode::Public, Mode::Constant, None);
    //     check_add_assign::<Circuit, u16, 16>(Mode::Public, Mode::Constant, None);
    // }
    //
    // #[test]
    // fn test_u16_add_public_public() {
    //     check_add::<Circuit, u16, 16>(Mode::Public, Mode::Public, 1, 32, 93, 218);
    //     check_add_assign::<Circuit, u16, 16>(Mode::Public, Mode::Public, 1, 32, 93, 218);
    // }
    //
    // #[test]
    // fn test_u16_add_public_private() {
    //     check_add::<Circuit, u16, 16>(Mode::Public, Mode::Private, 1, 16, 109, 218);
    //     check_add_assign::<Circuit, u16, 16>(Mode::Public, Mode::Private, 1, 16, 109, 218);
    // }
    //
    // #[test]
    // fn test_u16_add_private_constant() {
    //     check_add::<Circuit, u16, 16>(Mode::Private, Mode::Constant, None);
    //     check_add_assign::<Circuit, u16, 16>(Mode::Private, Mode::Constant, None);
    // }
    //
    // #[test]
    // fn test_u16_add_private_public() {
    //     check_add::<Circuit, u16, 16>(Mode::Private, Mode::Public, 1, 16, 109, 218);
    //     check_add_assign::<Circuit, u16, 16>(Mode::Private, Mode::Public, 1, 16, 109, 218);
    // }
    //
    // #[test]
    // fn test_u16_add_private_private() {
    //     check_add::<Circuit, u16, 16>(Mode::Private, Mode::Private, 1, 0, 125, 218);
    //     check_add_assign::<Circuit, u16, 16>(Mode::Private, Mode::Private, 1, 0, 125, 218);
    // }
    //
    // // Tests for i32
    //
    // #[test]
    // fn test_u32_add_constant_constant() {
    //     check_add::<Circuit, u32, 32>(Mode::Constant, Mode::Constant, 96, 0, 0, 0);
    //     check_add_assign::<Circuit, u32, 32>(Mode::Constant, Mode::Constant, 96, 0, 0, 0);
    // }
    //
    // #[test]
    // fn test_u32_add_constant_public() {
    //     check_add::<Circuit, u32, 32>(Mode::Constant, Mode::Public, None);
    //     check_add_assign::<Circuit, u32, 32>(Mode::Constant, Mode::Public, None);
    // }
    //
    // #[test]
    // fn test_u32_add_constant_private() {
    //     check_add::<Circuit, u32, 32>(Mode::Constant, Mode::Private, None);
    //     check_add_assign::<Circuit, u32, 32>(Mode::Constant, Mode::Private, None);
    // }
    //
    // #[test]
    // fn test_u32_add_public_constant() {
    //     check_add::<Circuit, u32, 32>(Mode::Public, Mode::Constant, None);
    //     check_add_assign::<Circuit, u32, 32>(Mode::Public, Mode::Constant, None);
    // }
    //
    // #[test]
    // fn test_u32_add_public_public() {
    //     check_add::<Circuit, u32, 32>(Mode::Public, Mode::Public, 1, 64, 189, 442);
    //     check_add_assign::<Circuit, u32, 32>(Mode::Public, Mode::Public, 1, 64, 189, 442);
    // }
    //
    // #[test]
    // fn test_u32_add_public_private() {
    //     check_add::<Circuit, u32, 32>(Mode::Public, Mode::Private, 1, 32, 221, 442);
    //     check_add_assign::<Circuit, u32, 32>(Mode::Public, Mode::Private, 1, 32, 221, 442);
    // }
    //
    // #[test]
    // fn test_u32_add_private_constant() {
    //     check_add::<Circuit, u32, 32>(Mode::Private, Mode::Constant, None);
    //     check_add_assign::<Circuit, u32, 32>(Mode::Private, Mode::Constant, None);
    // }
    //
    // #[test]
    // fn test_u32_add_private_public() {
    //     check_add::<Circuit, u32, 32>(Mode::Private, Mode::Public, 1, 32, 221, 442);
    //     check_add_assign::<Circuit, u32, 32>(Mode::Private, Mode::Public, 1, 32, 221, 442);
    // }
    //
    // #[test]
    // fn test_u32_add_private_private() {
    //     check_add::<Circuit, u32, 32>(Mode::Private, Mode::Private, 1, 0, 253, 442);
    //     check_add_assign::<Circuit, u32, 32>(Mode::Private, Mode::Private, 1, 0, 253, 442);
    // }
    //
    // // Tests for i64
    //
    // #[test]
    // fn test_u64_add_constant_constant() {
    //     check_add::<Circuit, u64, 64>(Mode::Constant, Mode::Constant, 192, 0, 0, 0);
    //     check_add_assign::<Circuit, u64, 64>(Mode::Constant, Mode::Constant, 192, 0, 0, 0);
    // }
    //
    // #[test]
    // fn test_u64_add_constant_public() {
    //     check_add::<Circuit, u64, 64>(Mode::Constant, Mode::Public, None);
    //     check_add_assign::<Circuit, u64, 64>(Mode::Constant, Mode::Public, None);
    // }
    //
    // #[test]
    // fn test_u64_add_constant_private() {
    //     check_add::<Circuit, u64, 64>(Mode::Constant, Mode::Private, None);
    //     check_add_assign::<Circuit, u64, 64>(Mode::Constant, Mode::Private, None);
    // }
    //
    // #[test]
    // fn test_u64_add_public_constant() {
    //     check_add::<Circuit, u64, 64>(Mode::Public, Mode::Constant, None);
    //     check_add_assign::<Circuit, u64, 64>(Mode::Public, Mode::Constant, None);
    // }
    //
    // #[test]
    // fn test_u64_add_public_public() {
    //     check_add::<Circuit, u64, 64>(Mode::Public, Mode::Public, 1, 128, 381, 890);
    //     check_add_assign::<Circuit, u64, 64>(Mode::Public, Mode::Public, 1, 128, 381, 890);
    // }
    //
    // #[test]
    // fn test_u64_add_public_private() {
    //     check_add::<Circuit, u64, 64>(Mode::Public, Mode::Private, 1, 64, 445, 890);
    //     check_add_assign::<Circuit, u64, 64>(Mode::Public, Mode::Private, 1, 64, 445, 890);
    // }
    //
    // #[test]
    // fn test_u64_add_private_constant() {
    //     check_add::<Circuit, u64, 64>(Mode::Private, Mode::Constant, None);
    //     check_add_assign::<Circuit, u64, 64>(Mode::Private, Mode::Constant, None);
    // }
    //
    // #[test]
    // fn test_u64_add_private_public() {
    //     check_add::<Circuit, u64, 64>(Mode::Private, Mode::Public, 1, 64, 445, 890);
    //     check_add_assign::<Circuit, u64, 64>(Mode::Private, Mode::Public, 1, 64, 445, 890);
    // }
    //
    // #[test]
    // fn test_u64_add_private_private() {
    //     check_add::<Circuit, u64, 64>(Mode::Private, Mode::Private, 1, 0, 509, 890);
    //     check_add_assign::<Circuit, u64, 64>(Mode::Private, Mode::Private, 1, 0, 509, 890);
    // }
    //
    // // Tests for i128
    //
    // #[test]
    // fn test_u128_add_constant_constant() {
    //     check_add::<Circuit, u128, 128>(Mode::Constant, Mode::Constant, 384, 0, 0, 0);
    //     check_add_assign::<Circuit, u128, 128>(Mode::Constant, Mode::Constant, 384, 0, 0, 0);
    // }
    //
    // #[test]
    // fn test_u128_add_constant_public() {
    //     check_add::<Circuit, u128, 128>(Mode::Constant, Mode::Public, None);
    //     check_add_assign::<Circuit, u128, 128>(Mode::Constant, Mode::Public, None);
    // }
    //
    // #[test]
    // fn test_u128_add_constant_private() {
    //     check_add::<Circuit, u128, 128>(Mode::Constant, Mode::Private, None);
    //     check_add_assign::<Circuit, u128, 128>(Mode::Constant, Mode::Private, None);
    // }
    //
    // #[test]
    // fn test_u128_add_public_constant() {
    //     check_add::<Circuit, u128, 128>(Mode::Public, Mode::Constant, None);
    //     check_add_assign::<Circuit, u128, 128>(Mode::Public, Mode::Constant, None);
    // }
    //
    // #[test]
    // fn test_u128_add_public_public() {
    //     check_add::<Circuit, u128, 128>(Mode::Public, Mode::Public, 1, 256, 765, 1786);
    //     check_add_assign::<Circuit, u128, 128>(Mode::Public, Mode::Public, 1, 256, 765, 1786);
    // }
    //
    // #[test]
    // fn test_u128_add_public_private() {
    //     check_add::<Circuit, u128, 128>(Mode::Public, Mode::Private, 1, 128, 893, 1786);
    //     check_add_assign::<Circuit, u128, 128>(Mode::Public, Mode::Private, 1, 128, 893, 1786);
    // }
    //
    // #[test]
    // fn test_u128_add_private_constant() {
    //     check_add::<Circuit, u128, 128>(Mode::Private, Mode::Constant, None);
    //     check_add_assign::<Circuit, u128, 128>(Mode::Private, Mode::Constant, None);
    // }
    //
    // #[test]
    // fn test_u128_add_private_public() {
    //     check_add::<Circuit, u128, 128>(Mode::Private, Mode::Public, 1, 128, 893, 1786);
    //     check_add_assign::<Circuit, u128, 128>(Mode::Private, Mode::Public, 1, 128, 893, 1786);
    // }
    //
    // #[test]
    // fn test_u128_add_private_private() {
    //     check_add::<Circuit, u128, 128>(Mode::Private, Mode::Private, 1, 0, 1021, 1786);
    //     check_add_assign::<Circuit, u128, 128>(Mode::Private, Mode::Private, 1, 0, 1021, 1786);
    // }
}
