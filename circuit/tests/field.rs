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
//! [Run a single test]: `cargo test field::add -- --show-output`
//!

extern crate snarkvm_circuit;

#[cfg(test)]
mod field {
    use snarkvm_circuit::{Boolean, Itertools};
    use snarkvm_circuit_environment::{Circuit, Environment, FromBits, Inject, Inverse, Mode, SquareRoot};
    use snarkvm_circuit_types::{Compare, DivUnchecked, Double, Equal, Field, Pow, Square, Ternary};
    use snarkvm_console_types_field::{Field as ConsoleField, One, Zero};
    use std::ops::{BitAnd, BitOr};

    #[test]
    fn add() {
        // no constraints
        let a = Field::<Circuit>::new(Mode::Private, ConsoleField::zero());
        let b = Field::<Circuit>::new(Mode::Private, ConsoleField::one());
        let _candidate = &a + &b;

        // print Circuit to JSON in console
        let circuit_json = Circuit::json();
        let output = serde_json::to_string_pretty(&circuit_json).unwrap();
        println!("// add");
        println!("{}", output);
    }

    #[test]
    fn compare() {
        let a = Field::<Circuit>::new(Mode::Private, ConsoleField::zero());
        let b = Field::<Circuit>::new(Mode::Private, ConsoleField::one());
        let _candidate = a.is_less_than(&b);

        // print Circuit to JSON in console
        let circuit_json = Circuit::json();
        let output = serde_json::to_string_pretty(&circuit_json).unwrap();
        println!("// compare");
        println!("{}", output);
    }

    #[test]
    fn div() {
        let a = Field::<Circuit>::new(Mode::Private, ConsoleField::zero());
        let b = Field::<Circuit>::new(Mode::Private, ConsoleField::one());
        let _candidate = &a / &b;

        // print Circuit to JSON in console
        let circuit_json = Circuit::json();
        let output = serde_json::to_string_pretty(&circuit_json).unwrap();
        println!("// div");
        println!("{}", output);
    }

    #[test]
    fn div_unchecked() {
        let a = Field::<Circuit>::new(Mode::Private, ConsoleField::zero());
        let b = Field::<Circuit>::new(Mode::Private, ConsoleField::one());
        let _candidate = a.div_unchecked(&b);

        // print Circuit to JSON in console
        let circuit_json = Circuit::json();
        let output = serde_json::to_string_pretty(&circuit_json).unwrap();
        println!("// div_unchecked");
        println!("{}", output);
    }

    #[test]
    fn double() {
        // no constraints
        let a = Field::<Circuit>::new(Mode::Private, ConsoleField::zero());
        let _candidate = a.double();

        // print Circuit to JSON in console
        let circuit_json = Circuit::json();
        let output = serde_json::to_string_pretty(&circuit_json).unwrap();
        println!("// double");
        println!("{}", output);
    }

    #[test]
    fn equal() {
        let a = Field::<Circuit>::new(Mode::Private, ConsoleField::zero());
        let b = Field::<Circuit>::new(Mode::Private, ConsoleField::one());
        let _candidate = a.is_not_equal(&b);

        // print Circuit to JSON in console
        let circuit_json = Circuit::json();
        let output = serde_json::to_string_pretty(&circuit_json).unwrap();
        println!("// equal");
        println!("{}", output);
    }

    #[test]
    fn from_bits_le() {
        let mut bits = vec![];
        for _i in 0..256 {
            bits.push(Boolean::<Circuit>::new(Mode::Private, false));
        }
        let _candidate = Field::<Circuit>::from_bits_le(&bits);

        // print Circuit to JSON in console
        let circuit_json = Circuit::json();
        let output = serde_json::to_string_pretty(&circuit_json).unwrap();
        println!("// from_bits_le");
        println!("{}", output);
    }

    #[test]
    fn from_bits_le_diff_const() {
        let mut bits = vec![];
        for _i in 0..10 {
            bits.push(Boolean::<Circuit>::new(Mode::Private, false));
        }
        let mut constant = vec![true, true, true, false, false, false, true, true, false, true];
        let is_lte = !constant.iter().zip_eq(bits).fold(Boolean::constant(false), |rest_is_less, (this, that)| {
            if *this { that.bitand(&rest_is_less) } else { that.bitor(&rest_is_less) }
        });
        Circuit::assert(is_lte);

        // print Circuit to JSON in console
        let circuit_json = Circuit::json();
        let output = serde_json::to_string_pretty(&circuit_json).unwrap();
        println!("// from_bits_le");
        println!("{}", output);
    }

    #[test]
    fn inverse() {
        let a = Field::<Circuit>::new(Mode::Private, ConsoleField::zero());
        let _candidate = a.inverse();

        // print Circuit to JSON in console
        let circuit_json = Circuit::json();
        let output = serde_json::to_string_pretty(&circuit_json).unwrap();
        println!("// inverse");
        println!("{}", output);
    }

    #[test]
    fn mul() {
        let a = Field::<Circuit>::new(Mode::Private, ConsoleField::zero());
        let b = Field::<Circuit>::new(Mode::Private, ConsoleField::one());
        let _candidate = &a * &b;

        // print Circuit to JSON in console
        let circuit_json = Circuit::json();
        let output = serde_json::to_string_pretty(&circuit_json).unwrap();
        println!("// mul");
        println!("{}", output);
    }

    #[test]
    fn neg() {
        // no constraints
        let a = Field::<Circuit>::new(Mode::Private, ConsoleField::zero());
        let _candidate = -&a;

        // print Circuit to JSON in console
        let circuit_json = Circuit::json();
        let output = serde_json::to_string_pretty(&circuit_json).unwrap();
        println!("// neg");
        println!("{}", output);
    }

    #[test]
    fn pow10() {
        let one = ConsoleField::one();
        let two = one + one;
        let four = two + two;
        let eight = four + four;
        let ten = eight + two;

        let a = Field::<Circuit>::new(Mode::Private, ConsoleField::zero());
        let b = Field::<Circuit>::new(Mode::Constant, ten);

        let _candidate = a.pow(&b);

        // print Circuit to JSON in console
        let circuit_json = Circuit::json();
        let output = serde_json::to_string_pretty(&circuit_json).unwrap();
        println!("// pow10");
        println!("{}", output);
    }

    #[test]
    fn pow() {
        let a = Field::<Circuit>::new(Mode::Private, ConsoleField::zero());
        let b = Field::<Circuit>::new(Mode::Private, ConsoleField::one());
        let _candidate = a.pow(&b);

        // print Circuit to JSON in console
        let circuit_json = Circuit::json();
        let output = serde_json::to_string_pretty(&circuit_json).unwrap();
        println!("// pow");
        println!("{}", output);
    }

    #[test]
    fn square() {
        // no constraints
        let a = Field::<Circuit>::new(Mode::Private, ConsoleField::zero());
        let _candidate = a.square();

        // print Circuit to JSON in console
        let circuit_json = Circuit::json();
        let output = serde_json::to_string_pretty(&circuit_json).unwrap();
        println!("// square");
        println!("{}", output);
    }

    #[test]
    fn square_root() {
        // no constraints
        let a = Field::<Circuit>::new(Mode::Private, ConsoleField::zero());
        let _candidate = a.square_root();

        // print Circuit to JSON in console
        let circuit_json = Circuit::json();
        let output = serde_json::to_string_pretty(&circuit_json).unwrap();
        println!("// square_root");
        println!("{}", output);
    }

    #[test]
    fn sub() {
        // no constraints
        let a = Field::<Circuit>::new(Mode::Private, ConsoleField::zero());
        let b = Field::<Circuit>::new(Mode::Private, ConsoleField::one());
        let _candidate = &a - &b;

        // print Circuit to JSON in console
        let circuit_json = Circuit::json();
        let output = serde_json::to_string_pretty(&circuit_json).unwrap();
        println!("// sub");
        println!("{}", output);
    }

    #[test]
    fn ternary() {
        let condition = Boolean::<Circuit>::new(Mode::Private, true);
        let a = Field::<Circuit>::new(Mode::Private, ConsoleField::zero());
        let b = Field::<Circuit>::new(Mode::Private, ConsoleField::one());
        let _candidate = Field::ternary(&condition, &a, &b);

        // print Circuit to JSON in console
        let circuit_json = Circuit::json();
        let output = serde_json::to_string_pretty(&circuit_json).unwrap();
        println!("// ternary");
        println!("{}", output);
    }
}
