// Copyright (C) 2019-2023 Aleo Systems Inc.
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

//! This test file will output JSON R1CS files for group gadgets in `circuits/types/group/`
//!
//! [Run all tests]: `cargo test -- --show-output`
//!
//! [Run a single test]: `cargo test group::add -- --show-output`
//!

extern crate snarkvm_circuit;

#[cfg(test)]
mod group {
    use snarkvm_circuit::{Boolean, FromStr, Itertools};
    use snarkvm_circuit_environment::{
        Environment,
        FormalCircuit,
        FromBits,
        Inject,
        Inverse,
        Mode,
        SquareRoot,
        ToBits,
        Transcribe,
    };
    use snarkvm_circuit_types::{Compare, DivUnchecked, Double, Equal, Field, Group, Ternary};
    use snarkvm_console_types_group::{Group as ConsoleGroup, Zero};
    use std::ops::{BitAnd, BitOr};

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

}
