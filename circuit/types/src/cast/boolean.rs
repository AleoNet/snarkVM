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
    use crate::Cast as CircuitCast;
    use snarkvm_circuit_environment::{Circuit, Count, Eject, Inject, Mode};

    use console::{network::Testnet3, types::Cast as ConsoleCast};

    use std::fmt::Debug;

    fn check_cast<CircuitType, ConsoleType>(mode: Mode, count: Count)
    where
        CircuitType: Eject,
        <CircuitType as Eject>::Primitive: Debug + PartialEq<ConsoleType>,
        ConsoleType: Debug,
        console::types::Boolean<Testnet3>: ConsoleCast<ConsoleType>,
        Boolean<Circuit>: CircuitCast<CircuitType>,
    {
        for value in [true, false] {
            let a = Boolean::<Circuit>::new(mode, value);
            match console::types::Boolean::new(value).cast() {
                // If the console implementation produces a result, then check that the circuit implementation
                // produces the same result and that the circuit is satisfied.
                Ok(expected) => {
                    Circuit::scope("test", || {
                        let candidate: CircuitType = a.cast();
                        assert_eq!(candidate.eject_value(), expected);
                        assert!(Circuit::is_satisfied_in_scope());
                        println!("mode: {:?}", mode);
                        println!("num_constants: {:?}", Circuit::num_constants_in_scope());
                        println!("num_public: {:?}", Circuit::num_public_in_scope());
                        println!("num_private: {:?}", Circuit::num_private_in_scope());
                        println!("num_constraints: {:?}", Circuit::num_constraints_in_scope());
                        assert!(count.matches(
                            Circuit::num_constants_in_scope(),
                            Circuit::num_public_in_scope(),
                            Circuit::num_private_in_scope(),
                            Circuit::num_constraints_in_scope()
                        ))
                    });
                }
                // Otherwise, check that the circuit is not satisfied.
                Err(_) => {
                    Circuit::scope("test", || {
                        let _: CircuitType = a.cast();
                        assert!(!Circuit::is_satisfied_in_scope());
                        println!("mode: {:?}", mode);
                        println!("num_constants: {:?}", Circuit::num_constants_in_scope());
                        println!("num_public: {:?}", Circuit::num_public_in_scope());
                        println!("num_private: {:?}", Circuit::num_private_in_scope());
                        println!("num_constraints: {:?}", Circuit::num_constraints_in_scope());
                        assert!(count.matches(
                            Circuit::num_constants_in_scope(),
                            Circuit::num_public_in_scope(),
                            Circuit::num_private_in_scope(),
                            Circuit::num_constraints_in_scope()
                        ))
                    });
                }
            }
            Circuit::reset();
        }
    }

    #[test]
    fn test_boolean_to_address() {
        check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Constant, Count::is(0, 0, 0, 0));
        check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Public, Count::is(0, 0, 0, 0));
        check_cast::<Address<Circuit>, console::types::Address<Testnet3>>(Mode::Private, Count::is(0, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_field() {
        check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Constant, Count::is(0, 0, 0, 0));
        check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Public, Count::is(0, 0, 0, 0));
        check_cast::<Field<Circuit>, console::types::Field<Testnet3>>(Mode::Private, Count::is(0, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_group() {
        check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Constant, Count::is(0, 0, 0, 0));
        check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Public, Count::is(0, 0, 0, 0));
        check_cast::<Group<Circuit>, console::types::Group<Testnet3>>(Mode::Private, Count::is(0, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_i8() {
        check_cast::<I8<Circuit>, console::types::I8<Testnet3>>(Mode::Constant, Count::is(0, 0, 0, 0));
        check_cast::<I8<Circuit>, console::types::I8<Testnet3>>(Mode::Public, Count::is(0, 0, 0, 0));
        check_cast::<I8<Circuit>, console::types::I8<Testnet3>>(Mode::Private, Count::is(0, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_i16() {
        check_cast::<I16<Circuit>, console::types::I16<Testnet3>>(Mode::Constant, Count::is(0, 0, 0, 0));
        check_cast::<I16<Circuit>, console::types::I16<Testnet3>>(Mode::Public, Count::is(0, 0, 0, 0));
        check_cast::<I16<Circuit>, console::types::I16<Testnet3>>(Mode::Private, Count::is(0, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_i32() {
        check_cast::<I32<Circuit>, console::types::I32<Testnet3>>(Mode::Constant, Count::is(0, 0, 0, 0));
        check_cast::<I32<Circuit>, console::types::I32<Testnet3>>(Mode::Public, Count::is(0, 0, 0, 0));
        check_cast::<I32<Circuit>, console::types::I32<Testnet3>>(Mode::Private, Count::is(0, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_i64() {
        check_cast::<I64<Circuit>, console::types::I64<Testnet3>>(Mode::Constant, Count::is(0, 0, 0, 0));
        check_cast::<I64<Circuit>, console::types::I64<Testnet3>>(Mode::Public, Count::is(0, 0, 0, 0));
        check_cast::<I64<Circuit>, console::types::I64<Testnet3>>(Mode::Private, Count::is(0, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_scalar() {
        check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Constant, Count::is(0, 0, 0, 0));
        check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Public, Count::is(0, 0, 0, 0));
        check_cast::<Scalar<Circuit>, console::types::Scalar<Testnet3>>(Mode::Private, Count::is(0, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_i128() {
        check_cast::<I128<Circuit>, console::types::I128<Testnet3>>(Mode::Constant, Count::is(0, 0, 0, 0));
        check_cast::<I128<Circuit>, console::types::I128<Testnet3>>(Mode::Public, Count::is(0, 0, 0, 0));
        check_cast::<I128<Circuit>, console::types::I128<Testnet3>>(Mode::Private, Count::is(0, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_u8() {
        check_cast::<U8<Circuit>, console::types::U8<Testnet3>>(Mode::Constant, Count::is(0, 0, 0, 0));
        check_cast::<U8<Circuit>, console::types::U8<Testnet3>>(Mode::Public, Count::is(0, 0, 0, 0));
        check_cast::<U8<Circuit>, console::types::U8<Testnet3>>(Mode::Private, Count::is(0, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_u16() {
        check_cast::<U16<Circuit>, console::types::U16<Testnet3>>(Mode::Constant, Count::is(0, 0, 0, 0));
        check_cast::<U16<Circuit>, console::types::U16<Testnet3>>(Mode::Public, Count::is(0, 0, 0, 0));
        check_cast::<U16<Circuit>, console::types::U16<Testnet3>>(Mode::Private, Count::is(0, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_u32() {
        check_cast::<U32<Circuit>, console::types::U32<Testnet3>>(Mode::Constant, Count::is(0, 0, 0, 0));
        check_cast::<U32<Circuit>, console::types::U32<Testnet3>>(Mode::Public, Count::is(0, 0, 0, 0));
        check_cast::<U32<Circuit>, console::types::U32<Testnet3>>(Mode::Private, Count::is(0, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_u64() {
        check_cast::<U64<Circuit>, console::types::U64<Testnet3>>(Mode::Constant, Count::is(128, 0, 0, 0));
        check_cast::<U64<Circuit>, console::types::U64<Testnet3>>(Mode::Public, Count::is(, 0, 0, 0));
        check_cast::<U64<Circuit>, console::types::U64<Testnet3>>(Mode::Private, Count::is(0, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_u128() {
        check_cast::<U128<Circuit>, console::types::U128<Testnet3>>(Mode::Constant, Count::is(256, 0, 0, 0));
        check_cast::<U128<Circuit>, console::types::U128<Testnet3>>(Mode::Public, Count::is(0, 0, 0, 0));
        check_cast::<U128<Circuit>, console::types::U128<Testnet3>>(Mode::Private, Count::is(0, 0, 0, 0));
    }
}
