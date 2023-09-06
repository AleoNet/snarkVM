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

//! This test file will output JSON R1CS files for i128 gadgets in `circuit/types/integers/`
//!
//! [Run all tests]: `cargo test -- --show-output`
//!
//! [Run a single test]: `cargo test i128::add -- --show-output`
//!

extern crate snarkvm_circuit;

#[cfg(test)]
mod i128 {
    use snarkvm_circuit::{I128, U8};
    use snarkvm_circuit_environment::{FormalCircuit, Inject, Mode, Transcribe};
    use snarkvm_console_types_integers::{
        AddWrapped,
        MulWrapped,
        PowChecked,
        PowWrapped,
        SubWrapped,
        Zero,
        I128 as ConsoleI128,
        U8 as ConsoleU8,
    };

    // for ops see circuit/types/integers/{add_checked,add_wrapped}.rs

    // var + var
    #[test]
    fn add_checked_var_var() {
        let a = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(0i128));
        let b = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let _candidate = &a + &b; // '+' on integers turns into a.add_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// add (checked) i128 private var with i128 private var");
        println!("{}", output);
    }

    // add constant 0
    #[test]
    fn add_checked_0_var() {
        let a = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::zero());
        let b = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let _candidate = &a + &b; // '+' on integers turns into a.add_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// add (checked) 0i128 constant with i128 private var");
        println!("{}", output);
    }

    // add constant 1
    #[test]
    fn add_checked_1_var() {
        let a = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::new(1i128));
        let b = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let _candidate = &a + &b; // '+' on integers turns into a.add_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// add (checked) 1i128 constant with i128 private var");
        println!("{}", output);
    }

    // add constant -2
    #[test]
    fn add_checked_neg2_var() {
        let a = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::new(-2i128));
        let b = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let _candidate = &a + &b; // '+' on integers turns into a.add_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// add (checked) -2i128 constant with i128 private var");
        println!("{}", output);
    }

    // add constant -2 in the other order
    #[test]
    fn add_checked_var_1() {
        let a = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let b = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::new(-2i128));
        let _candidate = &a + &b; // '+' on integers turns into a.add_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// add (checked) i128 private var with -2i128 constant");
        println!("{}", output);
    }

    // Try adding a larger constant.  This is 2^63 - 2.
    // Note, this constant can also be made with ConsoleI128::from_str("9223372036854775806I128").unwrap());
    #[test]
    fn add_checked_N_var() {
        let a = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::new(9223372036854775806i128));
        let b = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let _candidate = &a + &b; // '+' on integers turns into a.add_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// add (checked) large i128 constant with i128 private var");
        println!("{}", output);
    }

    #[test]
    fn add_wrapped_var_var() {
        let a = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(0i128));
        let b = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let _candidate = &a.add_wrapped(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// add (wrapped) i128 private var with i128 private var");
        println!("{}", output);
    }

    // We don't need to do as many samples for add_wrapped, since it is simpler, but we do both directions of constant.
    #[test]
    fn add_wrapped_neg6_var() {
        let a = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::new(-6i128));
        let b = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let _candidate = &a.add_wrapped(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// add (wrapped) -6i128 constant with i128 private var");
        println!("{}", output);
    }

    #[test]
    fn add_wrapped_var_neg6() {
        let a = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let b = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::new(-6i128));
        let _candidate = &a.add_wrapped(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// add (wrapped) i128 private var with -6i128 constant");
        println!("{}", output);
    }

    #[test]
    fn add_wrapped_var_6() {
        let a = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let b = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::new(6i128));
        let _candidate = &a.add_wrapped(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// add (wrapped) i128 private var with 6i128 constant");
        println!("{}", output);
    }

    // for op see circuit/types/integers/and.rs

    // var & var
    #[test]
    fn and_var_var() {
        let a = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(0i128));
        let b = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let _candidate = &a & &b; // '&' on integers turns into a.and(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// and i128 private var with i128 private var");
        println!("{}", output);
    }

    // for ops see circuit/types/integers/{sub_checked,sub_wrapped}.rs

    // var - var
    #[test]
    fn sub_checked_var_var() {
        let a = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(0i128));
        let b = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let _candidate = &a - &b; // '-' on integers turns into a.sub_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// sub (checked) i128 private var with i128 private var");
        println!("{}", output);
    }

    // sub constant 0
    #[test]
    fn sub_checked_0_var() {
        let a = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::zero());
        let b = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let _candidate = &a - &b; // '-' on integers turns into a.sub_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// sub (checked) 0i128 constant with i128 private var");
        println!("{}", output);
    }

    // sub constant 1
    #[test]
    fn sub_checked_1_var() {
        let a = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::new(1i128));
        let b = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let _candidate = &a - &b; // '-' on integers turns into a.sub_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// sub (checked) 1i128 constant with i128 private var");
        println!("{}", output);
    }

    // sub constant -1
    #[test]
    fn sub_checked_neg1_var() {
        let a = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::new(-1i128));
        let b = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let _candidate = &a - &b; // '-' on integers turns into a.sub_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// sub (checked) -1i128 constant with i128 private var");
        println!("{}", output);
    }

    // sub constant 1 in the other order
    #[test]
    fn sub_checked_var_1() {
        let a = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let b = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::new(1i128));
        let _candidate = &a - &b; // '-' on integers turns into a.sub_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// sub (checked) i128 private var with 1i128 constant");
        println!("{}", output);
    }

    // sub constant -1 in the other order
    #[test]
    fn sub_checked_var_neg1() {
        let a = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let b = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::new(-1i128));
        let _candidate = &a - &b; // '-' on integers turns into a.sub_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// sub (checked) i128 private var with -1i128 constant");
        println!("{}", output);
    }

    // Try subing a larger constant.  This is 2^63 - 2.
    // Note, this constant can also be made with ConsoleI128::from_str("9223372036854775806I128").unwrap());
    #[test]
    fn sub_checked_N_var() {
        let a = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::new(9223372036854775806i128));
        let b = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let _candidate = &a - &b; // '-' on integers turns into a.sub_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// sub (checked) large i128 constant with i128 private var");
        println!("{}", output);
    }

    #[test]
    fn sub_wrapped_var_var() {
        let a = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(0i128));
        let b = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let _candidate = &a.sub_wrapped(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// sub (wrapped) i128 private var with i128 private var");
        println!("{}", output);
    }

    // We don't need to do as many samples for sub_wrapped, since it is simpler, but we do both directions of constant.
    #[test]
    fn sub_wrapped_6_var() {
        let a = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::new(6i128));
        let b = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let _candidate = &a.sub_wrapped(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// sub (wrapped) 6i128 constant with i128 private var");
        println!("{}", output);
    }

    #[test]
    fn sub_wrapped_neg6_var() {
        let a = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::new(-6i128));
        let b = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let _candidate = &a.sub_wrapped(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// sub (wrapped) -6i128 constant with i128 private var");
        println!("{}", output);
    }

    #[test]
    fn sub_wrapped_var_6() {
        let a = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let b = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::new(6i128));
        let _candidate = &a.sub_wrapped(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// sub (wrapped) i128 private var with 6i128 constant ");
        println!("{}", output);
    }

    // for ops see circuit/types/integers/{mul_checked,mul_wrapped}.rs

    // mul with carry of var and var
    #[test]
    fn mul_with_carry_var_var() {
        let a = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(0i128));
        let b = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let (_candidate1, _candidate2) = snarkvm_circuit_types::integers::I128::mul_with_carry(&a, &b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// mul with carry i128 private var with i128 private var");
        println!("{}", output);
    }

    // var * var
    #[test]
    fn mul_checked_var_var() {
        let a = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(0i128));
        let b = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let _candidate = &a * &b; // '*' on integers turns into a.mul_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// mul (checked) i128 private var with i128 private var");
        println!("{}", output);
    }

    // mul constant 0
    #[test]
    fn mul_checked_0_var() {
        let a = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::zero());
        let b = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let _candidate = &a * &b; // '*' on integers turns into a.mul_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// mul (checked) 0i128 constant with i128 private var");
        println!("{}", output);
    }

    // mul constant 1
    #[test]
    fn mul_checked_1_var() {
        let a = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::new(1i128));
        let b = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let _candidate = &a * &b; // '*' on integers turns into a.mul_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// mul (checked) 1i128 constant with i128 private var");
        println!("{}", output);
    }

    // mul constant 1 in the other order
    #[test]
    fn mul_checked_var_1() {
        let a = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let b = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::new(1i128));
        let _candidate = &a * &b; // '*' on integers turns into a.mul_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// mul (checked) i128 private var with 1i128 constant");
        println!("{}", output);
    }

    // Try muling a larger constant.  This is 2^64 - 2.
    // Note, this constant can also be made with ConsoleI128::from_str("9223372036854775806I128").unwrap());
    #[test]
    fn mul_checked_N_var() {
        let a = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::new(9223372036854775806i128));
        let b = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let _candidate = &a * &b; // '*' on integers turns into a.mul_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// mul (checked) large i128 constant with i128 private var");
        println!("{}", output);
    }

    #[test]
    fn mul_wrapped_var_var() {
        let a = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(0i128));
        let b = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let _candidate = &a.mul_wrapped(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// mul (wrapped) i128 private var with i128 private var");
        println!("{}", output);
    }

    // We don't need to do as many samples for mul_wrapped, since it is simpler, but we do both directions of constant.
    #[test]
    fn mul_wrapped_6_var() {
        let a = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::new(6i128));
        let b = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let _candidate = &a.mul_wrapped(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// mul (wrapped) 6i128 constant with i128 private var");
        println!("{}", output);
    }

    #[test]
    fn mul_wrapped_var_6() {
        let a = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let b = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::new(6i128));
        let _candidate = &a.mul_wrapped(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// mul (wrapped) i128 private var with 6i128 constant");
        println!("{}", output);
    }

    #[test]
    fn mul_wrapped_var_neg6() {
        let a = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let b = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::new(-6i128));
        let _candidate = &a.mul_wrapped(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// mul (wrapped) i128 private var with -6i128 constant");
        println!("{}", output);
    }

    // var.pow_checked(var) i.e., the `pow` opcode
    #[test]
    fn pow_checked_var_var() {
        // Note that the exponent type is limited to u8, u16, or u32.
        let a = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(0i128));
        let b = U8::<FormalCircuit>::new(Mode::Private, ConsoleU8::new(1u8));
        let _candidate = &a.pow_checked(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// pow_checked i128 private var with u8 private var");
        println!("{}", output);
    }

    // const.pow_checked(var) 10**var
    #[test]
    fn pow_checked_const_var() {
        // Note that the exponent type is limited to u8, u16, or u32.
        let a = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::new(10i128));
        let b = U8::<FormalCircuit>::new(Mode::Private, ConsoleU8::new(1u8));
        let _candidate = &a.pow_checked(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// pow_checked 10i128 constant with u8 private var");
        println!("{}", output);
    }

    // const.pow_checked(var) (-10)**var
    #[test]
    fn pow_checked_negconst_var() {
        // Note that the exponent type is limited to u8, u16, or u32.
        let a = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::new(-10i128));
        let b = U8::<FormalCircuit>::new(Mode::Private, ConsoleU8::new(1u8));
        let _candidate = &a.pow_checked(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// pow_checked -10i128 constant with u8 private var");
        println!("{}", output);
    }

    // var.pow_checked(const) var**10
    #[test]
    fn pow_checked_var_const() {
        // Note that the exponent type is limited to u8, u16, or u32.
        let a = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(0i128));
        let b = U8::<FormalCircuit>::new(Mode::Constant, ConsoleU8::new(10u8));
        let _candidate = &a.pow_checked(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// pow_checked i128 private var with u8 constant");
        println!("{}", output);
    }

    // var.pow_wrapped(var)
    #[test]
    fn pow_wrapped_var_var() {
        // Note that the exponent type is limited to u8, u16, or u32.
        let a = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(0i128));
        let b = U8::<FormalCircuit>::new(Mode::Private, ConsoleU8::new(1u8));
        let _candidate = &a.pow_wrapped(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// pow_wrapped i128 private var with u8 private var");
        println!("{}", output);
    }

    // const.pow_wrapped(var)
    #[test]
    fn pow_wrapped_const_var() {
        // Note that the exponent type is limited to u8, u16, or u32.
        let a = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::new(10i128));
        let b = U8::<FormalCircuit>::new(Mode::Private, ConsoleU8::new(1u8));
        let _candidate = &a.pow_wrapped(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// pow_wrapped 10i128 const with u8 private var");
        println!("{}", output);
    }

    // const.pow_wrapped(var)
    #[test]
    fn pow_wrapped_negconst_var() {
        // Note that the exponent type is limited to u8, u16, or u32.
        let a = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::new(-10i128));
        let b = U8::<FormalCircuit>::new(Mode::Private, ConsoleU8::new(1u8));
        let _candidate = &a.pow_wrapped(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// pow_wrapped -10i128 const with u8 private var");
        println!("{}", output);
    }

    // var.pow_wrapped(const)
    #[test]
    fn pow_wrapped_var_const() {
        // Note that the exponent type is limited to u8, u16, or u32.
        let a = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(0i128));
        let b = U8::<FormalCircuit>::new(Mode::Constant, ConsoleU8::new(10u8));
        let _candidate = &a.pow_wrapped(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// pow_wrapped i128 private var with u8 const");
        println!("{}", output);
    }

    // for ops see circuit/types/integers/{div_checked,div_wrapped}.rs
    // TODO: get samples of signed div_wrapped.

    // var / var
    #[test]
    fn div_checked_var_var() {
        let a = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(0i128));
        let b = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let _candidate = &a / &b; // '/' on integers turns into a.div_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// div (checked) i128 private var with i128 private var");
        println!("{}", output);
    }

    // div constant 0
    #[test]
    fn div_checked_0_var() {
        let a = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::zero());
        let b = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let _candidate = &a / &b; // '/' on integers turns into a.div_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// div (checked) 0i128 constant with i128 private var");
        println!("{}", output);
    }

    // div constant 1
    #[test]
    fn div_checked_1_var() {
        let a = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::new(1i128));
        let b = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let _candidate = &a / &b; // '/' on integers turns into a.div_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// div (checked) 1i128 constant with i128 private var");
        println!("{}", output);
    }

    // div constant -1
    #[test]
    fn div_checked_neg1_var() {
        let a = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::new(-1i128));
        let b = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let _candidate = &a / &b; // '/' on integers turns into a.div_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// div (checked) -1i128 constant with i128 private var");
        println!("{}", output);
    }

    // div constant 1 in the other order
    #[test]
    fn div_checked_var_1() {
        let a = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let b = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::new(1i128));
        let _candidate = &a / &b; // '/' on integers turns into a.div_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// div (checked) i128 private var with 1i128 constant");
        println!("{}", output);
    }

    // div constant -1 in the other order
    #[test]
    fn div_checked_var_neg1() {
        let a = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let b = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::new(-1i128));
        let _candidate = &a / &b; // '/' on integers turns into a.div_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// div (checked) i128 private var with -1i128 constant");
        println!("{}", output);
    }

    // Try dividing a larger constant.  This is 2^63 - 2.
    #[test]
    fn div_checked_N_var() {
        let a = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::new(9223372036854775806i128));
        let b = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let _candidate = &a / &b; // '/' on integers turns into a.div_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// div. (checked) large i128 constant with i128 private var");
        println!("{}", output);
    }

    #[test]
    fn div_checked_var_N() {
        let a = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let b = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::new(9223372036854775806i128));
        let _candidate = &a / &b; // '/' on integers turns into a.div_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// div. (checked) i128 private var with large i128 constant");
        println!("{}", output);
    }

    // Try dividing a larger negative constant.  This is -(2^63 - 2).
    #[test]
    fn div_checked_negN_var() {
        let a = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::new(-9223372036854775806i128));
        let b = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let _candidate = &a / &b; // '/' on integers turns into a.div_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// div. (checked) large negative i128 constant with i128 private var");
        println!("{}", output);
    }

    #[test]
    fn div_checked_var_negN() {
        let a = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let b = I128::<FormalCircuit>::new(Mode::Constant, ConsoleI128::new(-9223372036854775806i128));
        let _candidate = &a / &b; // '/' on integers turns into a.div_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// div. (checked) i128 private var with large negative i128 constant");
        println!("{}", output);
    }

    // Note, modulo is not defined on signed integer types; see circuit/types/integers/modulo.rs

    // for op see circuit/types/integers/not.rs
    // !var
    #[test]
    fn not_var() {
        let a = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(0i128));
        let _candidate = !&a; // '!' on integers turns into a.not()

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// not i128 private var");
        println!("{}", output);
    }

    // for op see circuit/types/integers/or.rs

    // var | var
    #[test]
    fn or_var_var() {
        let a = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(0i128));
        let b = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let _candidate = &a | &b; // '|' on integers turns into a.or(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// or i128 private var with i128 private var");
        println!("{}", output);
    }

    // for ops see circuit/types/integers/{rem_checked,rem_wrapped}.rs
    // TODO: get samples of signed rem_wrapped.

    // var % var
    #[test]
    fn rem_checked_var_var() {
        let a = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(0i128));
        let b = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let _candidate = &a % &b; // '%' on integers turns into a.rem_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// rem (checked) i128 private var with i128 private var");
        println!("{}", output);
    }

    // for op see circuit/types/integers/xor.rs

    // var ^ var
    #[test]
    fn xor_var_var() {
        let a = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(0i128));
        let b = I128::<FormalCircuit>::new(Mode::Private, ConsoleI128::new(1i128));
        let _candidate = &a ^ &b; // '^' on integers turns into a.xor(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// xor i128 private var with i128 private var");
        println!("{}", output);
    }
}
