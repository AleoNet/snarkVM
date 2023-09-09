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

//! This test file will output JSON R1CS files for address gadgets in `circuits/types/address/`
//!
//! [Run all tests]: `cargo test -- --show-output`
//!
//! [Run a single test]: `cargo test address::add -- --show-output`
//!

extern crate snarkvm_circuit;

// The opcodes that are address specific are: assert.eq assert.neq is.eq is.neq ternary
// They are implemented in circuit/types/address/src/{compare,equal,ternary}.rs
// Similar to field and group, there is also a directory of helpers circuit/types/address/src/helpers/

#[cfg(test)]
mod address {
    use snarkvm_circuit::{
        prelude::{Compare, Equal, Ternary},
        Boolean,
    };
    use snarkvm_circuit_environment::{FormalCircuit, Inject, Mode, Transcribe};
    use snarkvm_circuit_types::Address;
    use snarkvm_console_types_address::{Address as ConsoleAddress}; // One, Zero not published

    use snarkvm_console_types_group::{Group as ConsoleGroup, Zero};

    // Note: although the comparison opcodes such as gt are not supported on addresses,
    // there is a compare method.  So we extract and test it in case it is used elsewhere.

    #[test]
    fn compare() {
        // Note, rand() and zero() are deprecated and not published, so
        // to get a witness ConsoleAddress we use `new` initialized from 0group.

        let a = Address::<FormalCircuit>::new(Mode::Private, ConsoleAddress::new(ConsoleGroup::zero()));
        let b = Address::<FormalCircuit>::new(Mode::Private, ConsoleAddress::new(ConsoleGroup::zero()));
        let _candidate = a.is_less_than(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// compare");
        println!("{}", output);
    }

    #[test]
    fn equal() {
        let a = Address::<FormalCircuit>::new(Mode::Private, ConsoleAddress::new(ConsoleGroup::zero()));
        let b = Address::<FormalCircuit>::new(Mode::Private, ConsoleAddress::new(ConsoleGroup::zero()));
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
        let a = Address::<FormalCircuit>::new(Mode::Private, ConsoleAddress::new(ConsoleGroup::zero()));
        let b = Address::<FormalCircuit>::new(Mode::Private, ConsoleAddress::new(ConsoleGroup::zero()));
        let _candidate = Address::ternary(&condition, &a, &b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// ternary");
        println!("{}", output);
    }


}
