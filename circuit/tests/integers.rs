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

//! This test file will output JSON R1CS files for field gadgets in `circuits/types/integers/`
//!
//! [Run all tests]: `cargo test -- --show-output`
//!
//! [Run a single test]: `cargo test integers::add -- --show-output`
//!

extern crate snarkvm_circuit;

#[cfg(test)]
mod integers {
    use snarkvm_circuit::U64;
    use snarkvm_circuit_environment::{FormalCircuit, Inject, Mode, Transcribe};
    use snarkvm_console_types_integers::U64 as ConsoleU64;

    #[test]
    fn add() {
        // no constraints
        let a = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(0u64));
        let b = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(1u64));
        let _candidate = &a + &b;

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// add u64 private with u64 private ");
        println!("{}", output);
    }
}
