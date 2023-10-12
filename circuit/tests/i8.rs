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

//! This test file will output JSON R1CS files for i8 gadgets in `circuit/types/integers/`
//!
//! [Run all tests]: `cargo test -- --show-output`
//!
//! [Run a single test]: `cargo test i8::shl_checked_var_var -- --show-output`
//!

extern crate snarkvm_circuit;

#[cfg(test)]
mod i8 {
    use snarkvm_circuit::{Boolean, I8, U8};
    use snarkvm_circuit_environment::{FormalCircuit, Inject, Mode, Transcribe};
    use snarkvm_console_types_integers::{
        AbsChecked,
        AbsWrapped,
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
        I8 as ConsoleI8,
        U8 as ConsoleU8,
    };

    #[test]
    fn shl_checked_var_var() {
        let a = I8::<FormalCircuit>::new(Mode::Private, ConsoleI8::new(1i8));
        let b = U8::<FormalCircuit>::new(Mode::Private, ConsoleU8::new(1u8));
        let _candidate = &a << &b; // '<<' on integers turns into a.shl_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string(&transcript).unwrap();
        println!("// shl (checked) i8 private var with u8 private var");
        println!("{}", output);
    }

    #[test]
    fn shl_wrapped_var_var() {
        let a = I8::<FormalCircuit>::new(Mode::Private, ConsoleI8::new(1i8));
        let b = U8::<FormalCircuit>::new(Mode::Private, ConsoleU8::new(1u8));
        let _candidate = &a.shl_wrapped(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string(&transcript).unwrap();
        println!("// shl (wrapped) i8 private var with u8 private var");
        println!("{}", output);
    }

    #[test]
    fn shr_checked_var_var() {
        let a = I8::<FormalCircuit>::new(Mode::Private, ConsoleI8::new(1i8));
        let b = U8::<FormalCircuit>::new(Mode::Private, ConsoleU8::new(1u8));
        let _candidate = &a >> &b; // '>>' on integers turns into a.shr_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string(&transcript).unwrap();
        println!("// shr (checked) i8 private var with u8 private var");
        println!("{}", output);
    }

    #[test]
    fn shr_wrapped_var_var() {
        let a = I8::<FormalCircuit>::new(Mode::Private, ConsoleI8::new(1i8));
        let b = U8::<FormalCircuit>::new(Mode::Private, ConsoleU8::new(1u8));
        let _candidate = &a.shr_wrapped(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string(&transcript).unwrap();
        println!("// shr (wrapped) i8 private var with u8 private var");
        println!("{}", output);
    }

}
