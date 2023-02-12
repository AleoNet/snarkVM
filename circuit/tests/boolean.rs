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

//! This test file will output JSON R1CS files for boolean gadgets in `circuits/types/boolean/`
//!
//! [Run all tests]: `cargo test -- --show-output`
//!
//! [Run a single test]: `cargo test boolean::and -- --show-output`
//!

extern crate snarkvm_circuit;

#[cfg(test)]
mod boolean {
    use crate::snarkvm_circuit::*;

    #[test]
    fn and() {
        let a = Boolean::<Circuit>::new(Mode::Private, true);
        let b = Boolean::<Circuit>::new(Mode::Private, false);
        // true AND false
        let _candidate = &a & &b;

        // print Circuit to JSON in console
        let circuit_json = Circuit::json();
        let output = serde_json::to_string_pretty(&circuit_json).unwrap();
        println!("// and");
        println!("{}", output);
    }

    #[test]
    fn equal() {
        let a = Boolean::<Circuit>::new(Mode::Private, true);
        let b = Boolean::<Circuit>::new(Mode::Private, false);
        // true == false
        let _candidate = a.is_equal(&b);

        // print Circuit to JSON in console
        let circuit_json = Circuit::json();
        let output = serde_json::to_string_pretty(&circuit_json).unwrap();
        println!("// equal");
        println!("{}", output);
    }

    #[test]
    fn nand() {
        let a = Boolean::<Circuit>::new(Mode::Private, true);
        let b = Boolean::<Circuit>::new(Mode::Private, false);
        // true NAND false
        let _candidate = a.nand(&b);

        // print Circuit to JSON in console
        let circuit_json = Circuit::json();
        let output = serde_json::to_string_pretty(&circuit_json).unwrap();
        println!("// nand");
        println!("{}", output);
    }

    #[test]
    fn nor() {
        let a = Boolean::<Circuit>::new(Mode::Private, true);
        let b = Boolean::<Circuit>::new(Mode::Private, false);
        // true NOR false
        let _candidate = a.nor(&b);

        // print Circuit to JSON in console
        let circuit_json = Circuit::json();
        let output = serde_json::to_string_pretty(&circuit_json).unwrap();
        println!("// nor");
        println!("{}", output);
    }

    #[test]
    fn not() {
        let a = Boolean::<Circuit>::new(Mode::Private, true);
        // NOT true
        let _candidate = !a;

        // print Circuit to JSON in console
        let circuit_json = Circuit::json();
        let output = serde_json::to_string_pretty(&circuit_json).unwrap();
        println!("// not");
        println!("{}", output);
    }

    #[test]
    fn or() {
        let a = Boolean::<Circuit>::new(Mode::Private, true);
        let b = Boolean::<Circuit>::new(Mode::Private, false);
        // true OR false
        let _candidate = &a | &b;

        // print Circuit to JSON in console
        let circuit_json = Circuit::json();
        let output = serde_json::to_string_pretty(&circuit_json).unwrap();
        println!("// or");
        println!("{}", output);
    }

    #[test]
    fn ternary() {
        let condition = Boolean::<Circuit>::new(Mode::Private, true);
        let a = Boolean::<Circuit>::new(Mode::Private, true);
        let b = Boolean::<Circuit>::new(Mode::Private, false);
        // if true ? true : false
        let _candidate = Boolean::ternary(&condition, &a, &b);

        // print Circuit to JSON in console
        let circuit_json = Circuit::json();
        let output = serde_json::to_string_pretty(&circuit_json).unwrap();
        println!("// ternary");
        println!("{}", output);
    }

    #[test]
    fn xor() {
        let a = Boolean::<Circuit>::new(Mode::Private, true);
        let b = Boolean::<Circuit>::new(Mode::Private, false);
        // true XOR false
        let _candidate = &a ^ &b;

        // print Circuit to JSON in console
        let circuit_json = Circuit::json();
        let output = serde_json::to_string_pretty(&circuit_json).unwrap();
        println!("// xor");
        println!("{}", output);
    }
}
