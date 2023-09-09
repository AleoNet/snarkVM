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

//! This test file will output JSON R1CS files for scalar gadgets in `circuits/types/scalar/`
//!
//! [Run all tests]: `cargo test -- --show-output`
//!
//! [Run a single test]: `cargo test scalar::add -- --show-output`
//!

extern crate snarkvm_circuit;

// The opcodes that are scalar specific are: assert.eq assert.neq gt gte is.eq is.neq lt lte ternary
// They are implemented in circuit/types/scalar/src/{add,compare,equal,ternary}.rs
// Similar to field and group, there is also a directory of helpers circuit/types/scalar/src/helpers/

// Note: scalar does not currently support `neg` and `sub`.
// Note: `group mul scalar` is defined in groups.

#[cfg(test)]
mod scalar {
    use snarkvm_circuit::{
        prelude::{Compare, Equal, Ternary},
        Boolean,
    };
    use snarkvm_circuit_environment::{FormalCircuit, Inject, Mode, Transcribe};
    use snarkvm_circuit_types::Scalar;
    use snarkvm_console_types_scalar::{Scalar as ConsoleScalar, Zero, One};

    #[test]
    fn add() {
        // scalar addition
        let a = Scalar::<FormalCircuit>::new(Mode::Private, ConsoleScalar::zero());
        let b = Scalar::<FormalCircuit>::new(Mode::Private, ConsoleScalar::zero());
        let _candidate = &a + &b;

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// add");
        println!("{}", output);
    }

    #[test]
    fn compare() {
        let a = Scalar::<FormalCircuit>::new(Mode::Private, ConsoleScalar::zero());
        let b = Scalar::<FormalCircuit>::new(Mode::Private, ConsoleScalar::one());
        let _candidate = a.is_less_than(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// compare");
        println!("{}", output);
    }

    #[test]
    fn equal() {
        let a = Scalar::<FormalCircuit>::new(Mode::Private, ConsoleScalar::zero());
        let b = Scalar::<FormalCircuit>::new(Mode::Private, ConsoleScalar::zero());
        let _candidate = a.is_equal(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// equal");
        println!("{}", output);
    }

    #[test]
    fn ternary() {
        let condition = Boolean::<FormalCircuit>::new(Mode::Private, true);
        let a = Scalar::<FormalCircuit>::new(Mode::Private, ConsoleScalar::zero());
        let b = Scalar::<FormalCircuit>::new(Mode::Private, ConsoleScalar::zero());
        let _candidate = Scalar::ternary(&condition, &a, &b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// ternary");
        println!("{}", output);
    }


}
