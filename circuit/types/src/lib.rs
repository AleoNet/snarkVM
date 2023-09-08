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

#![forbid(unsafe_code)]

pub mod cast;
pub use cast::*;

pub mod cast_lossy;
pub use cast_lossy::*;

pub use modules::*;

pub mod modules {
    pub use snarkvm_circuit_environment as environment;

    pub use snarkvm_circuit_types_address as address;
    pub use snarkvm_circuit_types_address::Address;

    pub use snarkvm_circuit_types_boolean as boolean;
    pub use snarkvm_circuit_types_boolean::Boolean;

    pub use snarkvm_circuit_types_field as field;
    pub use snarkvm_circuit_types_field::Field;

    pub use snarkvm_circuit_types_group as group;
    pub use snarkvm_circuit_types_group::Group;

    pub use snarkvm_circuit_types_integers as integers;
    pub use snarkvm_circuit_types_integers::{I128, I16, I32, I64, I8, U128, U16, U32, U64, U8};

    pub use snarkvm_circuit_types_scalar as scalar;
    pub use snarkvm_circuit_types_scalar::Scalar;

    pub use snarkvm_circuit_types_string as string;
    pub use snarkvm_circuit_types_string::StringType;
}

pub mod prelude {
    pub use crate::{cast::*, cast_lossy::*, modules::*};
    pub use snarkvm_circuit_environment::prelude::*;
}

#[cfg(test)]
mod test_helpers {
    macro_rules! impl_check_cast {
        ($fun:ident, $circuit_type:ty, $console_type:ty) => {
            fn check_cast<CircuitType, ConsoleType>(mode: Mode, count: UpdatableCount)
            where
                CircuitType: Eject,
                <CircuitType as Eject>::Primitive: Debug + PartialEq<ConsoleType>,
                ConsoleType: Debug,
                $console_type: ConsoleCast<ConsoleType>,
                $circuit_type: CircuitCast<CircuitType>,
            {
                let rng = &mut TestRng::default();
                for i in 0..ITERATIONS {
                    let (console_value, circuit_value) = sample_values(i, mode, rng);
                    match console_value.$fun() {
                        // If the console cast fails and the mode is constant, then the circuit cast should fail.
                        Err(_) if mode == Mode::Constant => {
                            assert!(std::panic::catch_unwind(|| circuit_value.$fun()).is_err())
                        }
                        // If the console cast fails, the circuit cast can either fail by panicking or fail by being unsatisfied.
                        Err(_) => {
                            Circuit::scope("test", || {
                                if std::panic::catch_unwind(|| circuit_value.$fun()).is_ok() {
                                    assert!(!Circuit::is_satisfied());
                                    count.assert_matches(
                                        Circuit::num_constants_in_scope(),
                                        Circuit::num_public_in_scope(),
                                        Circuit::num_private_in_scope(),
                                        Circuit::num_constraints_in_scope(),
                                    );
                                }
                            });
                        }
                        // If the console cast succeeds, the circuit cast should succeed and the values should match.
                        Ok(expected) => Circuit::scope("test", || {
                            let result = circuit_value.$fun();
                            assert_eq!(result.eject_value(), expected);
                            assert!(Circuit::is_satisfied());
                            count.assert_matches(
                                Circuit::num_constants_in_scope(),
                                Circuit::num_public_in_scope(),
                                Circuit::num_private_in_scope(),
                                Circuit::num_constraints_in_scope(),
                            );
                        }),
                    };
                    Circuit::reset();
                }
            }
        };
    }

    pub(super) use impl_check_cast;
}
