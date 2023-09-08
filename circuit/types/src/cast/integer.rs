// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;

impl<E: Environment, I: IntegerType> Cast<Address<E>> for Integer<E, I> {
    /// Casts an `Integer` to an `Address`.
    #[inline]
    fn cast(&self) -> Address<E> {
        let field: Field<E> = self.cast();
        field.cast()
    }
}

impl<E: Environment, I: IntegerType> Cast<Boolean<E>> for Integer<E, I> {
    /// Casts an `Integer` to a `Boolean`.
    #[inline]
    fn cast(&self) -> Boolean<E> {
        let is_one = self.is_one();
        E::assert(self.is_zero().bitor(&is_one));
        is_one
    }
}

impl<E: Environment, I: IntegerType> Cast<Field<E>> for Integer<E, I> {
    /// Casts an `Integer` to a `Field`.
    #[inline]
    fn cast(&self) -> Field<E> {
        self.to_field()
    }
}

impl<E: Environment, I: IntegerType> Cast<Group<E>> for Integer<E, I> {
    /// Casts an `Integer` to a `Group`.
    #[inline]
    fn cast(&self) -> Group<E> {
        let field: Field<E> = self.cast();
        field.cast()
    }
}

impl<E: Environment, I0: IntegerType, I1: IntegerType> Cast<Integer<E, I1>> for Integer<E, I0> {
    /// Casts an `Integer` to an `Integer`.
    #[inline]
    fn cast(&self) -> Integer<E, I1> {
        let bits_le = self.to_bits_le();
        Integer::<E, I1>::from_bits_le(&bits_le)
    }
}

impl<E: Environment, I: IntegerType> Cast<Scalar<E>> for Integer<E, I> {
    /// Casts an `Integer` to a `Scalar`.
    #[inline]
    fn cast(&self) -> Scalar<E> {
        let bits_le = self.to_bits_le();
        Scalar::<E>::from_bits_le(&bits_le)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{test_helpers::impl_check_cast, Cast as CircuitCast};

    use console::{
        network::Testnet3,
        prelude::{One, TestRng, Uniform, Zero},
        types::Cast as ConsoleCast,
    };
    use snarkvm_circuit_environment::{count_is, Circuit, Eject, Inject, Mode, UpdatableCount};

    use std::fmt::Debug;

    const ITERATIONS: usize = 100;

    fn sample_values<I: IntegerType>(
        i: usize,
        mode: Mode,
        rng: &mut TestRng,
    ) -> (console::types::integers::Integer<Testnet3, I>, Integer<Circuit, I>) {
        let console_value = match i {
            0 => console::types::integers::Integer::<Testnet3, I>::zero(),
            1 => console::types::integers::Integer::<Testnet3, I>::one(),
            2 => console::types::integers::Integer::<Testnet3, I>::new(I::MAX),
            3 => console::types::integers::Integer::<Testnet3, I>::new(I::MIN),
            4 if I::is_signed() => -console::types::integers::Integer::<Testnet3, I>::one(),
            _ => Uniform::rand(rng),
        };
        let circuit_value = Integer::<Circuit, I>::new(mode, console_value.clone());
        (console_value, circuit_value)
    }

    mod i8 {
        use super::*;

        fn sample_values(i: usize, mode: Mode, rng: &mut TestRng) -> (console::types::I8<Testnet3>, I8<Circuit>) {
            super::sample_values(i, mode, rng)
        }

        impl_check_cast!(cast, I8<Circuit>, console::types::I8<Testnet3>);

        #[test]
        fn test_i8_to_address() {
            check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Constant, count_is!(5, 0, 0, 0));
            check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Public, count_is!(4, 0, 15, 13));
            check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Private, count_is!(4, 0, 15, 13));
        }

        #[test]
        fn test_i8_to_boolean() {
            check_cast::<Boolean<Circuit>, console::types::Boolean<Testnet3>>(Mode::Constant, count_is!(16, 0, 0, 0));
            check_cast::<Boolean<Circuit>, console::types::Boolean<Testnet3>>(Mode::Public, count_is!(16, 0, 5, 8));
            check_cast::<Boolean<Circuit>, console::types::Boolean<Testnet3>>(Mode::Private, count_is!(16, 0, 5, 8));
        }

        #[test]
        fn test_i8_to_field() {
            check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i8_to_group() {
            check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Constant, count_is!(5, 0, 0, 0));
            check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Public, count_is!(4, 0, 15, 13));
            check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Private, count_is!(4, 0, 15, 13));
        }

        #[test]
        fn test_i8_to_i16() {
            check_cast::<I16<Circuit>, console::types::I16<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I16<Circuit>, console::types::I16<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I16<Circuit>, console::types::I16<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i8_to_i32() {
            check_cast::<I32<Circuit>, console::types::I32<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I32<Circuit>, console::types::I32<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I32<Circuit>, console::types::I32<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i8_to_i64() {
            check_cast::<I64<Circuit>, console::types::I64<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I64<Circuit>, console::types::I64<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I64<Circuit>, console::types::I64<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i8_to_i128() {
            check_cast::<I128<Circuit>, console::types::I128<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I128<Circuit>, console::types::I128<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I128<Circuit>, console::types::I128<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i8_to_scalar() {
            check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i8_to_u8() {
            check_cast::<U8<Circuit>, console::types::U8<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U8<Circuit>, console::types::U8<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U8<Circuit>, console::types::U8<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i8_to_u16() {
            check_cast::<U16<Circuit>, console::types::U16<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U16<Circuit>, console::types::U16<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U16<Circuit>, console::types::U16<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i8_to_u32() {
            check_cast::<U32<Circuit>, console::types::U32<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U32<Circuit>, console::types::U32<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U32<Circuit>, console::types::U32<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i8_to_u64() {
            check_cast::<U64<Circuit>, console::types::U64<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U64<Circuit>, console::types::U64<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U64<Circuit>, console::types::U64<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i8_to_u128() {
            check_cast::<U128<Circuit>, console::types::U128<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U128<Circuit>, console::types::U128<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U128<Circuit>, console::types::U128<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }
    }

    mod i16 {
        use super::*;

        fn sample_values(i: usize, mode: Mode, rng: &mut TestRng) -> (console::types::I16<Testnet3>, I16<Circuit>) {
            super::sample_values(i, mode, rng)
        }

        impl_check_cast!(cast, I16<Circuit>, console::types::I16<Testnet3>);

        #[test]
        fn test_i16_to_address() {
            check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Constant, count_is!(5, 0, 0, 0));
            check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Public, count_is!(4, 0, 15, 13));
            check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Private, count_is!(4, 0, 15, 13));
        }

        #[test]
        fn test_i16_to_boolean() {
            check_cast::<Boolean<Circuit>, console::types::Boolean<Testnet3>>(Mode::Constant, count_is!(32, 0, 0, 0));
            check_cast::<Boolean<Circuit>, console::types::Boolean<Testnet3>>(Mode::Public, count_is!(32, 0, 5, 8));
            check_cast::<Boolean<Circuit>, console::types::Boolean<Testnet3>>(Mode::Private, count_is!(32, 0, 5, 8));
        }

        #[test]
        fn test_i16_to_field() {
            check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i16_to_group() {
            check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Constant, count_is!(5, 0, 0, 0));
            check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Public, count_is!(4, 0, 15, 13));
            check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Private, count_is!(4, 0, 15, 13));
        }

        #[test]
        fn test_i16_to_i8() {
            check_cast::<I8<Circuit>, console::types::I8<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I8<Circuit>, console::types::I8<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I8<Circuit>, console::types::I8<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i16_to_i32() {
            check_cast::<I32<Circuit>, console::types::I32<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I32<Circuit>, console::types::I32<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I32<Circuit>, console::types::I32<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i16_to_i64() {
            check_cast::<I64<Circuit>, console::types::I64<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I64<Circuit>, console::types::I64<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I64<Circuit>, console::types::I64<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i16_to_i128() {
            check_cast::<I128<Circuit>, console::types::I128<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I128<Circuit>, console::types::I128<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I128<Circuit>, console::types::I128<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i16_to_scalar() {
            check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i16_to_u8() {
            check_cast::<U8<Circuit>, console::types::U8<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U8<Circuit>, console::types::U8<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 8));
            check_cast::<U8<Circuit>, console::types::U8<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 8));
        }

        #[test]
        fn test_i16_to_u16() {
            check_cast::<U16<Circuit>, console::types::U16<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U16<Circuit>, console::types::U16<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U16<Circuit>, console::types::U16<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i16_to_u32() {
            check_cast::<U32<Circuit>, console::types::U32<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U32<Circuit>, console::types::U32<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U32<Circuit>, console::types::U32<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i16_to_u64() {
            check_cast::<U64<Circuit>, console::types::U64<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U64<Circuit>, console::types::U64<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U64<Circuit>, console::types::U64<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i16_to_u128() {
            check_cast::<U128<Circuit>, console::types::U128<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U128<Circuit>, console::types::U128<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U128<Circuit>, console::types::U128<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }
    }

    mod i32 {
        use super::*;

        fn sample_values(i: usize, mode: Mode, rng: &mut TestRng) -> (console::types::I32<Testnet3>, I32<Circuit>) {
            super::sample_values(i, mode, rng)
        }

        impl_check_cast!(cast, I32<Circuit>, console::types::I32<Testnet3>);

        #[test]
        fn test_i32_to_address() {
            check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Constant, count_is!(5, 0, 0, 0));
            check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Public, count_is!(4, 0, 15, 13));
            check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Private, count_is!(4, 0, 15, 13));
        }

        #[test]
        fn test_i32_to_boolean() {
            check_cast::<Boolean<Circuit>, console::types::Boolean<Testnet3>>(Mode::Constant, count_is!(64, 0, 0, 0));
            check_cast::<Boolean<Circuit>, console::types::Boolean<Testnet3>>(Mode::Public, count_is!(64, 0, 5, 8));
            check_cast::<Boolean<Circuit>, console::types::Boolean<Testnet3>>(Mode::Private, count_is!(64, 0, 5, 8));
        }

        #[test]
        fn test_i32_to_field() {
            check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i32_to_group() {
            check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Constant, count_is!(5, 0, 0, 0));
            check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Public, count_is!(4, 0, 15, 13));
            check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Private, count_is!(4, 0, 15, 13));
        }

        #[test]
        fn test_i32_to_i8() {
            check_cast::<I8<Circuit>, console::types::I8<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I8<Circuit>, console::types::I8<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I8<Circuit>, console::types::I8<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i32_to_i16() {
            check_cast::<I16<Circuit>, console::types::I16<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I16<Circuit>, console::types::I16<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I16<Circuit>, console::types::I16<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i32_to_i64() {
            check_cast::<I64<Circuit>, console::types::I64<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I64<Circuit>, console::types::I64<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I64<Circuit>, console::types::I64<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i32_to_i128() {
            check_cast::<I128<Circuit>, console::types::I128<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I128<Circuit>, console::types::I128<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I128<Circuit>, console::types::I128<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i32_to_scalar() {
            check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i32_to_u8() {
            check_cast::<U8<Circuit>, console::types::U8<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U8<Circuit>, console::types::U8<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 24));
            check_cast::<U8<Circuit>, console::types::U8<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 24));
        }

        #[test]
        fn test_i32_to_u16() {
            check_cast::<U16<Circuit>, console::types::U16<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U16<Circuit>, console::types::U16<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 16));
            check_cast::<U16<Circuit>, console::types::U16<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 16));
        }

        #[test]
        fn test_i32_to_u32() {
            check_cast::<U32<Circuit>, console::types::U32<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U32<Circuit>, console::types::U32<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U32<Circuit>, console::types::U32<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i32_to_u64() {
            check_cast::<U64<Circuit>, console::types::U64<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U64<Circuit>, console::types::U64<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U64<Circuit>, console::types::U64<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i32_to_u128() {
            check_cast::<U128<Circuit>, console::types::U128<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U128<Circuit>, console::types::U128<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U128<Circuit>, console::types::U128<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }
    }

    mod i64 {
        use super::*;

        fn sample_values(i: usize, mode: Mode, rng: &mut TestRng) -> (console::types::I64<Testnet3>, I64<Circuit>) {
            super::sample_values(i, mode, rng)
        }

        impl_check_cast!(cast, I64<Circuit>, console::types::I64<Testnet3>);

        #[test]
        fn test_i64_to_address() {
            check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Constant, count_is!(5, 0, 0, 0));
            check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Public, count_is!(4, 0, 15, 13));
            check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Private, count_is!(4, 0, 15, 13));
        }

        #[test]
        fn test_i64_to_boolean() {
            check_cast::<Boolean<Circuit>, console::types::Boolean<Testnet3>>(Mode::Constant, count_is!(32, 0, 0, 0));
            check_cast::<Boolean<Circuit>, console::types::Boolean<Testnet3>>(Mode::Public, count_is!(32, 0, 5, 8));
            check_cast::<Boolean<Circuit>, console::types::Boolean<Testnet3>>(Mode::Private, count_is!(32, 0, 5, 8));
        }

        #[test]
        fn test_i64_to_field() {
            check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i64_to_group() {
            check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Constant, count_is!(5, 0, 0, 0));
            check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Public, count_is!(4, 0, 15, 13));
            check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Private, count_is!(4, 0, 15, 13));
        }

        #[test]
        fn test_i64_to_i8() {
            check_cast::<I8<Circuit>, console::types::I8<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I8<Circuit>, console::types::I8<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I8<Circuit>, console::types::I8<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i64_to_i16() {
            check_cast::<I16<Circuit>, console::types::I16<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I16<Circuit>, console::types::I16<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I16<Circuit>, console::types::I16<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i64_to_i32() {
            check_cast::<I32<Circuit>, console::types::I32<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I32<Circuit>, console::types::I32<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I32<Circuit>, console::types::I32<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i64_to_i128() {
            check_cast::<I128<Circuit>, console::types::I128<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I128<Circuit>, console::types::I128<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I128<Circuit>, console::types::I128<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i64_to_scalar() {
            check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i64_to_u8() {
            check_cast::<U8<Circuit>, console::types::U8<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U8<Circuit>, console::types::U8<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 8));
            check_cast::<U8<Circuit>, console::types::U8<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 8));
        }

        #[test]
        fn test_i64_to_u16() {
            check_cast::<U16<Circuit>, console::types::U16<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U16<Circuit>, console::types::U16<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U16<Circuit>, console::types::U16<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i64_to_u32() {
            check_cast::<U32<Circuit>, console::types::U32<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U32<Circuit>, console::types::U32<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U32<Circuit>, console::types::U32<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i64_to_u64() {
            check_cast::<U64<Circuit>, console::types::U64<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U64<Circuit>, console::types::U64<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U64<Circuit>, console::types::U64<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i64_to_u128() {
            check_cast::<U128<Circuit>, console::types::U128<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U128<Circuit>, console::types::U128<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U128<Circuit>, console::types::U128<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }
    }

    mod i128 {
        use super::*;

        fn sample_values(i: usize, mode: Mode, rng: &mut TestRng) -> (console::types::I128<Testnet3>, I128<Circuit>) {
            super::sample_values(i, mode, rng)
        }

        impl_check_cast!(cast, I128<Circuit>, console::types::I128<Testnet3>);

        #[test]
        fn test_i128_to_address() {
            check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Constant, count_is!(5, 0, 0, 0));
            check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Public, count_is!(4, 0, 15, 13));
            check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Private, count_is!(4, 0, 15, 13));
        }

        #[test]
        fn test_i128_to_boolean() {
            check_cast::<Boolean<Circuit>, console::types::Boolean<Testnet3>>(Mode::Constant, count_is!(64, 0, 0, 0));
            check_cast::<Boolean<Circuit>, console::types::Boolean<Testnet3>>(Mode::Public, count_is!(64, 0, 5, 8));
            check_cast::<Boolean<Circuit>, console::types::Boolean<Testnet3>>(Mode::Private, count_is!(64, 0, 5, 8));
        }

        #[test]
        fn test_i128_to_field() {
            check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i128_to_group() {
            check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Constant, count_is!(5, 0, 0, 0));
            check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Public, count_is!(4, 0, 15, 13));
            check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Private, count_is!(4, 0, 15, 13));
        }

        #[test]
        fn test_i128_to_i8() {
            check_cast::<I8<Circuit>, console::types::I8<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I8<Circuit>, console::types::I8<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I8<Circuit>, console::types::I8<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i128_to_i16() {
            check_cast::<I16<Circuit>, console::types::I16<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I16<Circuit>, console::types::I16<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I16<Circuit>, console::types::I16<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i128_to_i32() {
            check_cast::<I32<Circuit>, console::types::I32<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I32<Circuit>, console::types::I32<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I32<Circuit>, console::types::I32<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i128_to_i64() {
            check_cast::<I64<Circuit>, console::types::I64<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I64<Circuit>, console::types::I64<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I64<Circuit>, console::types::I64<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i128_to_scalar() {
            check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i128_to_u8() {
            check_cast::<U8<Circuit>, console::types::U8<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U8<Circuit>, console::types::U8<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 24));
            check_cast::<U8<Circuit>, console::types::U8<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 24));
        }

        #[test]
        fn test_i128_to_u16() {
            check_cast::<U16<Circuit>, console::types::U16<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U16<Circuit>, console::types::U16<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 16));
            check_cast::<U16<Circuit>, console::types::U16<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 16));
        }

        #[test]
        fn test_i128_to_u32() {
            check_cast::<U32<Circuit>, console::types::U32<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U32<Circuit>, console::types::U32<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U32<Circuit>, console::types::U32<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i128_to_u64() {
            check_cast::<U64<Circuit>, console::types::U64<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U64<Circuit>, console::types::U64<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U64<Circuit>, console::types::U64<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i128_to_u128() {
            check_cast::<U128<Circuit>, console::types::U128<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U128<Circuit>, console::types::U128<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U128<Circuit>, console::types::U128<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }
    }

    mod u8 {
        use super::*;

        fn sample_values(i: usize, mode: Mode, rng: &mut TestRng) -> (console::types::U8<Testnet3>, U8<Circuit>) {
            super::sample_values(i, mode, rng)
        }

        impl_check_cast!(cast, U8<Circuit>, console::types::U8<Testnet3>);

        #[test]
        fn test_u8_to_address() {
            check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Constant, count_is!(5, 0, 0, 0));
            check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Public, count_is!(4, 0, 15, 13));
            check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Private, count_is!(4, 0, 15, 13));
        }

        #[test]
        fn test_u8_to_boolean() {
            check_cast::<Boolean<Circuit>, console::types::Boolean<Testnet3>>(Mode::Constant, count_is!(16, 0, 0, 0));
            check_cast::<Boolean<Circuit>, console::types::Boolean<Testnet3>>(Mode::Public, count_is!(16, 0, 5, 8));
            check_cast::<Boolean<Circuit>, console::types::Boolean<Testnet3>>(Mode::Private, count_is!(16, 0, 5, 8));
        }

        #[test]
        fn test_u8_to_field() {
            check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u8_to_group() {
            check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Constant, count_is!(5, 0, 0, 0));
            check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Public, count_is!(4, 0, 15, 13));
            check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Private, count_is!(4, 0, 15, 13));
        }

        #[test]
        fn test_u8_to_i8() {
            check_cast::<I8<Circuit>, console::types::I8<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I8<Circuit>, console::types::I8<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I8<Circuit>, console::types::I8<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u8_to_i16() {
            check_cast::<I16<Circuit>, console::types::I16<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I16<Circuit>, console::types::I16<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I16<Circuit>, console::types::I16<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u8_to_i32() {
            check_cast::<I32<Circuit>, console::types::I32<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I32<Circuit>, console::types::I32<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I32<Circuit>, console::types::I32<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u8_to_i64() {
            check_cast::<I64<Circuit>, console::types::I64<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I64<Circuit>, console::types::I64<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I64<Circuit>, console::types::I64<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u8_to_i128() {
            check_cast::<I128<Circuit>, console::types::I128<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I128<Circuit>, console::types::I128<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I128<Circuit>, console::types::I128<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u8_to_scalar() {
            check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u8_to_u16() {
            check_cast::<U16<Circuit>, console::types::U16<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U16<Circuit>, console::types::U16<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U16<Circuit>, console::types::U16<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u8_to_u32() {
            check_cast::<U32<Circuit>, console::types::U32<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U32<Circuit>, console::types::U32<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U32<Circuit>, console::types::U32<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u8_to_u64() {
            check_cast::<U64<Circuit>, console::types::U64<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U64<Circuit>, console::types::U64<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U64<Circuit>, console::types::U64<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u8_to_u128() {
            check_cast::<U128<Circuit>, console::types::U128<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U128<Circuit>, console::types::U128<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U128<Circuit>, console::types::U128<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }
    }

    mod u16 {
        use super::*;

        fn sample_values(i: usize, mode: Mode, rng: &mut TestRng) -> (console::types::U16<Testnet3>, U16<Circuit>) {
            super::sample_values(i, mode, rng)
        }

        impl_check_cast!(cast, U16<Circuit>, console::types::U16<Testnet3>);

        #[test]
        fn test_u16_to_address() {
            check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Constant, count_is!(5, 0, 0, 0));
            check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Public, count_is!(4, 0, 15, 13));
            check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Private, count_is!(4, 0, 15, 13));
        }

        #[test]
        fn test_u16_to_boolean() {
            check_cast::<Boolean<Circuit>, console::types::Boolean<Testnet3>>(Mode::Constant, count_is!(32, 0, 0, 0));
            check_cast::<Boolean<Circuit>, console::types::Boolean<Testnet3>>(Mode::Public, count_is!(32, 0, 5, 8));
            check_cast::<Boolean<Circuit>, console::types::Boolean<Testnet3>>(Mode::Private, count_is!(32, 0, 5, 8));
        }

        #[test]
        fn test_u16_to_field() {
            check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u16_to_group() {
            check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Constant, count_is!(5, 0, 0, 0));
            check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Public, count_is!(4, 0, 15, 13));
            check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Private, count_is!(4, 0, 15, 13));
        }

        #[test]
        fn test_u16_to_i8() {
            check_cast::<I8<Circuit>, console::types::I8<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I8<Circuit>, console::types::I8<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I8<Circuit>, console::types::I8<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u16_to_i16() {
            check_cast::<I16<Circuit>, console::types::I16<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I16<Circuit>, console::types::I16<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I16<Circuit>, console::types::I16<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u16_to_i32() {
            check_cast::<I32<Circuit>, console::types::I32<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I32<Circuit>, console::types::I32<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I32<Circuit>, console::types::I32<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u16_to_i64() {
            check_cast::<I64<Circuit>, console::types::I64<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I64<Circuit>, console::types::I64<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I64<Circuit>, console::types::I64<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u16_to_i128() {
            check_cast::<I128<Circuit>, console::types::I128<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I128<Circuit>, console::types::I128<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I128<Circuit>, console::types::I128<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u16_to_scalar() {
            check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u16_to_u8() {
            check_cast::<U8<Circuit>, console::types::U8<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U8<Circuit>, console::types::U8<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 8));
            check_cast::<U8<Circuit>, console::types::U8<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 8));
        }

        #[test]
        fn test_u16_to_u32() {
            check_cast::<U32<Circuit>, console::types::U32<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U32<Circuit>, console::types::U32<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U32<Circuit>, console::types::U32<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u16_to_u64() {
            check_cast::<U64<Circuit>, console::types::U64<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U64<Circuit>, console::types::U64<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U64<Circuit>, console::types::U64<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u16_to_u128() {
            check_cast::<U128<Circuit>, console::types::U128<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U128<Circuit>, console::types::U128<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U128<Circuit>, console::types::U128<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }
    }

    mod u32 {
        use super::*;

        fn sample_values(i: usize, mode: Mode, rng: &mut TestRng) -> (console::types::U32<Testnet3>, U32<Circuit>) {
            super::sample_values(i, mode, rng)
        }

        impl_check_cast!(cast, U32<Circuit>, console::types::U32<Testnet3>);

        #[test]
        fn test_u32_to_address() {
            check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Constant, count_is!(5, 0, 0, 0));
            check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Public, count_is!(4, 0, 15, 13));
            check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Private, count_is!(4, 0, 15, 13));
        }

        #[test]
        fn test_u32_to_boolean() {
            check_cast::<Boolean<Circuit>, console::types::Boolean<Testnet3>>(Mode::Constant, count_is!(64, 0, 0, 0));
            check_cast::<Boolean<Circuit>, console::types::Boolean<Testnet3>>(Mode::Public, count_is!(64, 0, 5, 8));
            check_cast::<Boolean<Circuit>, console::types::Boolean<Testnet3>>(Mode::Private, count_is!(64, 0, 5, 8));
        }

        #[test]
        fn test_u32_to_field() {
            check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u32_to_group() {
            check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Constant, count_is!(5, 0, 0, 0));
            check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Public, count_is!(4, 0, 15, 13));
            check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Private, count_is!(4, 0, 15, 13));
        }

        #[test]
        fn test_u32_to_i8() {
            check_cast::<I8<Circuit>, console::types::I8<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I8<Circuit>, console::types::I8<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I8<Circuit>, console::types::I8<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u32_to_i16() {
            check_cast::<I16<Circuit>, console::types::I16<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I16<Circuit>, console::types::I16<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I16<Circuit>, console::types::I16<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u32_to_i32() {
            check_cast::<I32<Circuit>, console::types::I32<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I32<Circuit>, console::types::I32<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I32<Circuit>, console::types::I32<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u32_to_i64() {
            check_cast::<I64<Circuit>, console::types::I64<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I64<Circuit>, console::types::I64<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I64<Circuit>, console::types::I64<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u32_to_i128() {
            check_cast::<I128<Circuit>, console::types::I128<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I128<Circuit>, console::types::I128<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I128<Circuit>, console::types::I128<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u32_to_scalar() {
            check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u32_to_u8() {
            check_cast::<U8<Circuit>, console::types::U8<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U8<Circuit>, console::types::U8<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 24));
            check_cast::<U8<Circuit>, console::types::U8<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 24));
        }

        #[test]
        fn test_u32_to_u16() {
            check_cast::<U16<Circuit>, console::types::U16<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U16<Circuit>, console::types::U16<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 16));
            check_cast::<U16<Circuit>, console::types::U16<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 16));
        }

        #[test]
        fn test_u32_to_u64() {
            check_cast::<U64<Circuit>, console::types::U64<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U64<Circuit>, console::types::U64<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U64<Circuit>, console::types::U64<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u32_to_u128() {
            check_cast::<U128<Circuit>, console::types::U128<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U128<Circuit>, console::types::U128<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U128<Circuit>, console::types::U128<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }
    }

    mod u64 {
        use super::*;

        fn sample_values(i: usize, mode: Mode, rng: &mut TestRng) -> (console::types::U64<Testnet3>, U64<Circuit>) {
            super::sample_values(i, mode, rng)
        }

        impl_check_cast!(cast, U64<Circuit>, console::types::U64<Testnet3>);

        #[test]
        fn test_u64_to_address() {
            check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Constant, count_is!(5, 0, 0, 0));
            check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Public, count_is!(4, 0, 15, 13));
            check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Private, count_is!(4, 0, 15, 13));
        }

        #[test]
        fn test_u64_to_boolean() {
            check_cast::<Boolean<Circuit>, console::types::Boolean<Testnet3>>(Mode::Constant, count_is!(32, 0, 0, 0));
            check_cast::<Boolean<Circuit>, console::types::Boolean<Testnet3>>(Mode::Public, count_is!(32, 0, 5, 8));
            check_cast::<Boolean<Circuit>, console::types::Boolean<Testnet3>>(Mode::Private, count_is!(32, 0, 5, 8));
        }

        #[test]
        fn test_u64_to_field() {
            check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u64_to_group() {
            check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Constant, count_is!(5, 0, 0, 0));
            check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Public, count_is!(4, 0, 15, 13));
            check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Private, count_is!(4, 0, 15, 13));
        }

        #[test]
        fn test_u64_to_i8() {
            check_cast::<I8<Circuit>, console::types::I8<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I8<Circuit>, console::types::I8<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I8<Circuit>, console::types::I8<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u64_to_i16() {
            check_cast::<I16<Circuit>, console::types::I16<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I16<Circuit>, console::types::I16<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I16<Circuit>, console::types::I16<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u64_to_i32() {
            check_cast::<I32<Circuit>, console::types::I32<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I32<Circuit>, console::types::I32<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I32<Circuit>, console::types::I32<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u64_to_i64() {
            check_cast::<I64<Circuit>, console::types::I64<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I64<Circuit>, console::types::I64<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I64<Circuit>, console::types::I64<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u64_to_i128() {
            check_cast::<I128<Circuit>, console::types::I128<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I128<Circuit>, console::types::I128<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I128<Circuit>, console::types::I128<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u64_to_scalar() {
            check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u64_to_u8() {
            check_cast::<U8<Circuit>, console::types::U8<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U8<Circuit>, console::types::U8<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 8));
            check_cast::<U8<Circuit>, console::types::U8<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 8));
        }

        #[test]
        fn test_u64_to_u16() {
            check_cast::<U16<Circuit>, console::types::U16<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U16<Circuit>, console::types::U16<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U16<Circuit>, console::types::U16<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u64_to_u32() {
            check_cast::<U32<Circuit>, console::types::U32<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U32<Circuit>, console::types::U32<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U32<Circuit>, console::types::U32<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u64_to_u128() {
            check_cast::<U128<Circuit>, console::types::U128<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U128<Circuit>, console::types::U128<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U128<Circuit>, console::types::U128<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }
    }

    mod u128 {
        use super::*;

        fn sample_values(i: usize, mode: Mode, rng: &mut TestRng) -> (console::types::U128<Testnet3>, U128<Circuit>) {
            super::sample_values(i, mode, rng)
        }

        impl_check_cast!(cast, U128<Circuit>, console::types::U128<Testnet3>);

        #[test]
        fn test_u128_to_address() {
            check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Constant, count_is!(5, 0, 0, 0));
            check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Public, count_is!(4, 0, 15, 13));
            check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Private, count_is!(4, 0, 15, 13));
        }

        #[test]
        fn test_u128_to_boolean() {
            check_cast::<Boolean<Circuit>, console::types::Boolean<Testnet3>>(Mode::Constant, count_is!(64, 0, 0, 0));
            check_cast::<Boolean<Circuit>, console::types::Boolean<Testnet3>>(Mode::Public, count_is!(64, 0, 5, 8));
            check_cast::<Boolean<Circuit>, console::types::Boolean<Testnet3>>(Mode::Private, count_is!(64, 0, 5, 8));
        }

        #[test]
        fn test_u128_to_field() {
            check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u128_to_group() {
            check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Constant, count_is!(5, 0, 0, 0));
            check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Public, count_is!(4, 0, 15, 13));
            check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Private, count_is!(4, 0, 15, 13));
        }

        #[test]
        fn test_u128_to_i8() {
            check_cast::<I8<Circuit>, console::types::I8<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I8<Circuit>, console::types::I8<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I8<Circuit>, console::types::I8<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u128_to_i16() {
            check_cast::<I16<Circuit>, console::types::I16<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I16<Circuit>, console::types::I16<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I16<Circuit>, console::types::I16<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u128_to_i32() {
            check_cast::<I32<Circuit>, console::types::I32<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I32<Circuit>, console::types::I32<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I32<Circuit>, console::types::I32<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u128_to_i64() {
            check_cast::<I64<Circuit>, console::types::I64<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I64<Circuit>, console::types::I64<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I64<Circuit>, console::types::I64<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u128_to_i128() {
            check_cast::<I128<Circuit>, console::types::I128<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I128<Circuit>, console::types::I128<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I128<Circuit>, console::types::I128<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u128_to_scalar() {
            check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u128_to_u8() {
            check_cast::<U8<Circuit>, console::types::U8<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U8<Circuit>, console::types::U8<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 24));
            check_cast::<U8<Circuit>, console::types::U8<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 24));
        }

        #[test]
        fn test_u128_to_u16() {
            check_cast::<U16<Circuit>, console::types::U16<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U16<Circuit>, console::types::U16<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 16));
            check_cast::<U16<Circuit>, console::types::U16<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 16));
        }

        #[test]
        fn test_u128_to_u32() {
            check_cast::<U32<Circuit>, console::types::U32<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U32<Circuit>, console::types::U32<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U32<Circuit>, console::types::U32<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u128_to_u64() {
            check_cast::<U64<Circuit>, console::types::U64<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U64<Circuit>, console::types::U64<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U64<Circuit>, console::types::U64<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
        }
    }
}
