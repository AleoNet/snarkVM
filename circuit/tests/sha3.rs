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

//! This test file will output JSON R1CS files for u64 gadgets in `circuit/types/integers/`
//!
//! [Run all tests]: `cargo test -- --show-output`
//!
//! [Run a single test]: `cargo test u64::add -- --show-output`
//!

extern crate snarkvm_circuit;

#[cfg(test)]
mod sha3 {
    use snarkvm_circuit::{Aleo, U64, U8, FormalCircuit, FormalV0};
    use snarkvm_circuit_environment::{Inject, Mode, Modulo, ToBits, Transcribe};
    // use snarkvm_circuit_algorithms::keccak::{Hash};
    use snarkvm_console_types_integers::{
        AddWrapped,
        Compare,
        DivWrapped,
        Equal,
        MulWrapped,
        PowChecked,
        PowWrapped,
        RemWrapped,
        // ShlChecked, // we are using `<<`
        ShlWrapped,
        // ShrChecked, // we are using `>>`
        ShrWrapped,
        SubWrapped,
        Ternary,
        Zero,
        U64 as ConsoleU64,
        U8 as ConsoleU8,
    };

    // for ops see circuit/algorithms/src/keccak/hash.rs

    #[test]
    fn keccak_u8() {
        let a = U8::new(Mode::Private, ConsoleU8::new(0u8));
        let _candidate = FormalV0::hash_keccak256(&a.to_bits_le());

        let transcript = FormalV0::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();

        println!("// keccak256 of u8 private var");
        // print FormalCircuit to JSON in console
        // This is too big to run interactively in a default IntelliJ console
        println!("{}", output);
    }
    #[test]
    fn sha3_u64() {
        let a = U64::new(Mode::Private, ConsoleU64::new(0u64));
        let _candidate = FormalV0::hash_sha3_256(&a.to_bits_le());

        let transcript = FormalV0::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();

        println!("// sha3 of u64 private var");
        // print FormalCircuit to JSON in console
        // This is too big to run interactively in a default IntelliJ console
        println!("{}", output);
    }
}
