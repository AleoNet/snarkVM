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

    use console::{prelude::Console, Cast as ConsoleCast};

    use core::panic::UnwindSafe;
    use std::fmt::Debug;

    fn check_cast<CircuitType, ConsoleType>(name: &str, mode: Mode, count: Count)
    where
        CircuitType: Eject,
        <CircuitType as Eject>::Primitive: Debug + PartialEq<ConsoleType>,
        ConsoleType: Debug,
        console::Boolean<Console>: ConsoleCast<ConsoleType>,
        Boolean<Circuit>: CircuitCast<CircuitType>,
    {
        for value in [true, false] {
            let a = Boolean::<Circuit>::new(mode, value);
            let expected: ConsoleType = console::Boolean::new(value).cast().unwrap();
            Circuit::scope(name, || {
                let candidate: CircuitType = a.cast();
                assert_eq!(candidate.eject_value(), expected);
                assert!(Circuit::is_satisfied_in_scope());
                assert!(count.matches(
                    Circuit::num_constants_in_scope(),
                    Circuit::num_public_in_scope(),
                    Circuit::num_private_in_scope(),
                    Circuit::num_constraints_in_scope()
                ))
            });
            Circuit::reset();
        }
    }

    fn run_test<I: IntegerType + UnwindSafe>(mode: Mode) {}
}
