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
