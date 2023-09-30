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

//! This test file will output JSON R1CS files for group gadgets in `circuits/types/group/`
//!
//! [Run all tests]: `cargo test -- --show-output`
//!
//! [Run a single test]: `cargo test group::add -- --show-output`
//!

extern crate snarkvm_circuit;

#[cfg(test)]
mod group {
    use snarkvm_circuit::{
        prelude::{Double, Equal, Ternary},
        Boolean,
    };
    use snarkvm_circuit_environment::{FormalCircuit, Inject, Mode, Transcribe};
    use snarkvm_circuit_types::{Field, Group, Scalar};
    use snarkvm_console_types_field::{Field as ConsoleField, One};
    use snarkvm_console_types_group::{Group as ConsoleGroup, Zero};
    use snarkvm_console_types_scalar::{Scalar as ConsoleScalar};
    use std::{
        str::FromStr,
    };

    #[test]
    fn add() {
        // group addition
        let a = Group::<FormalCircuit>::new(Mode::Private, ConsoleGroup::zero());
        let b = Group::<FormalCircuit>::new(Mode::Private, ConsoleGroup::zero());
        let _candidate = &a + &b;

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// add");
        println!("{}", output);
    }

    #[test]
    fn double() {
        // no constraints
        let a = Group::<FormalCircuit>::new(Mode::Private, ConsoleGroup::zero());
        let _candidate = a.double();

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// double");
        println!("{}", output);
    }

    #[test]
    fn equal() {
        let a = Group::<FormalCircuit>::new(Mode::Private, ConsoleGroup::zero());
        let b = Group::<FormalCircuit>::new(Mode::Private, ConsoleGroup::zero());
        let _candidate = a.is_equal(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// equal");
        println!("{}", output);
    }

    #[test]
    fn neg() {
        let a = Group::<FormalCircuit>::new(Mode::Private, ConsoleGroup::zero());
        let _candidate = -&a;

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// neg");
        println!("{}", output);
    }

    #[test]
    fn sub() {
        let a = Group::<FormalCircuit>::new(Mode::Private, ConsoleGroup::zero());
        let b = Group::<FormalCircuit>::new(Mode::Private, ConsoleGroup::zero());
        let _candidate = &a - &b;

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// sub");
        println!("{}", output);
    }

    #[test]
    fn ternary() {
        let condition = Boolean::<FormalCircuit>::new(Mode::Private, true);
        let a = Group::<FormalCircuit>::new(Mode::Private, ConsoleGroup::zero());
        let b = Group::<FormalCircuit>::new(Mode::Private, ConsoleGroup::zero());
        let _candidate = Group::ternary(&condition, &a, &b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// ternary");
        println!("{}", output);
    }

    #[test]
    fn mul() {
        // multiplication of a group by a scalar
        let a = Scalar::<FormalCircuit>::new(Mode::Private, ConsoleScalar::zero());
        let b = Group::<FormalCircuit>::new(Mode::Private, ConsoleGroup::zero());
        let _candidate = &a * &b;

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// mul");
        println!("{}", output);
    }

    #[test]
    fn mul10() {
        // multiplication of a group by the constant 10scalar
        let ten = ConsoleScalar::from_str("10scalar");
        let a = Scalar::<FormalCircuit>::new(Mode::Constant, ten.unwrap());
        let b = Group::<FormalCircuit>::new(Mode::Private, ConsoleGroup::zero());
        let _candidate = &a * &b;

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// mul10");
        println!("{}", output);
    }

    #[test]
    fn from_xy_coordinates() {
        // see circuit/types/group/src/helpers/from_xy_coordinates.rs
        let x= Field::<FormalCircuit>::new(Mode::Private, ConsoleField::zero());
        let y = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::one());
        let _candidate = Group::<FormalCircuit>::from_xy_coordinates(x, y);

        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// from_xy_coordinates");
        println!("{}", output);
    }

}
