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

impl<E: Environment> Cast<Address<E>> for Boolean<E> {
    /// Casts a `Boolean` to an `Address`.
    #[inline]
    fn cast(&self) -> Address<E> {
        let field: Field<E> = self.cast();
        field.cast()
    }
}

impl<E: Environment> Cast<Boolean<E>> for Boolean<E> {
    /// Casts a `Boolean` to a `Boolean`.
    #[inline]
    fn cast(&self) -> Boolean<E> {
        self.clone()
    }
}

impl<E: Environment> Cast<Field<E>> for Boolean<E> {
    /// Casts a `Boolean` to a `Field`.
    #[inline]
    fn cast(&self) -> Field<E> {
        Field::from_boolean(self)
    }
}

impl<E: Environment> Cast<Group<E>> for Boolean<E> {
    /// Casts a `Boolean` to a `Group`.
    #[inline]
    fn cast(&self) -> Group<E> {
        let field: Field<E> = self.cast();
        field.cast()
    }
}

impl<E: Environment, I: IntegerType> Cast<Integer<E, I>> for Boolean<E> {
    /// Casts a `Boolean` to an `Integer`.
    #[inline]
    fn cast(&self) -> Integer<E, I> {
        Integer::ternary(self, &Integer::one(), &Integer::zero())
    }
}

impl<E: Environment> Cast<Scalar<E>> for Boolean<E> {
    /// Casts a `Boolean` to a `Scalar`.
    #[inline]
    fn cast(&self) -> Scalar<E> {
        Scalar::ternary(self, &Scalar::one(), &Scalar::zero())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{test_helpers::impl_check_cast, Cast as CircuitCast};
    use snarkvm_circuit_environment::{count_is, Circuit, Eject, Inject, Mode, UpdatableCount};

    use console::{network::Testnet3, prelude::TestRng, types::Cast as ConsoleCast};

    use std::fmt::Debug;

    const ITERATIONS: usize = 2;

    fn sample_values(i: usize, mode: Mode, _: &mut TestRng) -> (console::types::Boolean<Testnet3>, Boolean<Circuit>) {
        (console::types::Boolean::new(i % 2 == 0), Boolean::new(mode, i % 2 == 0))
    }

    impl_check_cast!(cast, Boolean<Circuit>, console::types::Boolean::<Testnet3>);

    #[test]
    fn test_boolean_to_address() {
        check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Constant, count_is!(5, 0, 0, 0));
        check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Public, count_is!(4, 0, 15, 13));
        check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Private, count_is!(4, 0, 15, 13));
    }

    #[test]
    fn test_boolean_to_boolean() {
        check_cast::<Boolean<Circuit>, console::types::Boolean<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
        check_cast::<Boolean<Circuit>, console::types::Boolean<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
        check_cast::<Boolean<Circuit>, console::types::Boolean<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_field() {
        check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Constant, count_is!(0, 0, 0, 0));
        check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Public, count_is!(0, 0, 0, 0));
        check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_group() {
        check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Constant, count_is!(5, 0, 0, 0));
        check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Public, count_is!(4, 0, 15, 13));
        check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Private, count_is!(4, 0, 15, 13));
    }

    #[test]
    fn test_boolean_to_i8() {
        check_cast::<I8<Circuit>, console::types::I8<Testnet3>>(Mode::Constant, count_is!(16, 0, 0, 0));
        check_cast::<I8<Circuit>, console::types::I8<Testnet3>>(Mode::Public, count_is!(16, 0, 0, 0));
        check_cast::<I8<Circuit>, console::types::I8<Testnet3>>(Mode::Private, count_is!(16, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_i16() {
        check_cast::<I16<Circuit>, console::types::I16<Testnet3>>(Mode::Constant, count_is!(32, 0, 0, 0));
        check_cast::<I16<Circuit>, console::types::I16<Testnet3>>(Mode::Public, count_is!(32, 0, 0, 0));
        check_cast::<I16<Circuit>, console::types::I16<Testnet3>>(Mode::Private, count_is!(32, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_i32() {
        check_cast::<I32<Circuit>, console::types::I32<Testnet3>>(Mode::Constant, count_is!(64, 0, 0, 0));
        check_cast::<I32<Circuit>, console::types::I32<Testnet3>>(Mode::Public, count_is!(64, 0, 0, 0));
        check_cast::<I32<Circuit>, console::types::I32<Testnet3>>(Mode::Private, count_is!(64, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_i64() {
        check_cast::<I64<Circuit>, console::types::I64<Testnet3>>(Mode::Constant, count_is!(128, 0, 0, 0));
        check_cast::<I64<Circuit>, console::types::I64<Testnet3>>(Mode::Public, count_is!(128, 0, 0, 0));
        check_cast::<I64<Circuit>, console::types::I64<Testnet3>>(Mode::Private, count_is!(128, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_i128() {
        check_cast::<I128<Circuit>, console::types::I128<Testnet3>>(Mode::Constant, count_is!(256, 0, 0, 0));
        check_cast::<I128<Circuit>, console::types::I128<Testnet3>>(Mode::Public, count_is!(256, 0, 0, 0));
        check_cast::<I128<Circuit>, console::types::I128<Testnet3>>(Mode::Private, count_is!(256, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_scalar() {
        check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Constant, count_is!(2, 0, 0, 0));
        check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Public, count_is!(2, 0, 0, 0));
        check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Private, count_is!(2, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_u8() {
        check_cast::<U8<Circuit>, console::types::U8<Testnet3>>(Mode::Constant, count_is!(16, 0, 0, 0));
        check_cast::<U8<Circuit>, console::types::U8<Testnet3>>(Mode::Public, count_is!(16, 0, 0, 0));
        check_cast::<U8<Circuit>, console::types::U8<Testnet3>>(Mode::Private, count_is!(16, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_u16() {
        check_cast::<U16<Circuit>, console::types::U16<Testnet3>>(Mode::Constant, count_is!(32, 0, 0, 0));
        check_cast::<U16<Circuit>, console::types::U16<Testnet3>>(Mode::Public, count_is!(32, 0, 0, 0));
        check_cast::<U16<Circuit>, console::types::U16<Testnet3>>(Mode::Private, count_is!(32, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_u32() {
        check_cast::<U32<Circuit>, console::types::U32<Testnet3>>(Mode::Constant, count_is!(64, 0, 0, 0));
        check_cast::<U32<Circuit>, console::types::U32<Testnet3>>(Mode::Public, count_is!(64, 0, 0, 0));
        check_cast::<U32<Circuit>, console::types::U32<Testnet3>>(Mode::Private, count_is!(64, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_u64() {
        check_cast::<U64<Circuit>, console::types::U64<Testnet3>>(Mode::Constant, count_is!(128, 0, 0, 0));
        check_cast::<U64<Circuit>, console::types::U64<Testnet3>>(Mode::Public, count_is!(128, 0, 0, 0));
        check_cast::<U64<Circuit>, console::types::U64<Testnet3>>(Mode::Private, count_is!(128, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_u128() {
        check_cast::<U128<Circuit>, console::types::U128<Testnet3>>(Mode::Constant, count_is!(256, 0, 0, 0));
        check_cast::<U128<Circuit>, console::types::U128<Testnet3>>(Mode::Public, count_is!(256, 0, 0, 0));
        check_cast::<U128<Circuit>, console::types::U128<Testnet3>>(Mode::Private, count_is!(256, 0, 0, 0));
    }
}
