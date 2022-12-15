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
//! [Run a single test]: `cargo test field::add -- --show-output`
//!

extern crate snarkvm_circuit;

#[cfg(test)]
mod field {
    use snarkvm_circuit::Boolean;
    use snarkvm_circuit_environment::{Circuit, Inject, Inverse, Mode, SquareRoot};
    use snarkvm_circuit_types::{Compare, DivUnchecked, Double, Equal, Field, Pow, Square, Ternary};
    use snarkvm_console_types_field::{Field as ConsoleField, One, Zero};

    #[test]
    fn add() { // no constraints
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
    fn double() { // no constraints
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
    fn neg() { // no constraints
        let a = Field::<Circuit>::new(Mode::Private, ConsoleField::zero());
        let _candidate = -&a;

        // print Circuit to JSON in console
        let circuit_json = Circuit::json();
        let output = serde_json::to_string_pretty(&circuit_json).unwrap();
        println!("// neg");
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
    fn square() { // no constraints
        let a = Field::<Circuit>::new(Mode::Private, ConsoleField::zero());
        let _candidate = a.square();

        // print Circuit to JSON in console
        let circuit_json = Circuit::json();
        let output = serde_json::to_string_pretty(&circuit_json).unwrap();
        println!("// square");
        println!("{}", output);
    }

    #[test]
    fn square_root() { // no constraints
        let a = Field::<Circuit>::new(Mode::Private, ConsoleField::zero());
        let _candidate = a.square_root();

        // print Circuit to JSON in console
        let circuit_json = Circuit::json();
        let output = serde_json::to_string_pretty(&circuit_json).unwrap();
        println!("// square_root");
        println!("{}", output);
    }

    #[test]
    fn sub() { // no constraints
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
