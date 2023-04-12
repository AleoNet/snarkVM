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

//! This test file will output JSON R1CS files for field gadgets in `circuit/types/integers/`
//!
//! [Run all tests]: `cargo test -- --show-output`
//!
//! [Run a single test]: `cargo test integers::add -- --show-output`
//!

extern crate snarkvm_circuit;

#[cfg(test)]
mod integers {
    use snarkvm_circuit::{FromStr, U64};
    use snarkvm_circuit_environment::{Environment, FormalCircuit, FromBits, Inject, Mode, ToBits, Transcribe};
    use snarkvm_console_types_integers::{AddWrapped, MulWrapped, One, SubWrapped, Zero, U64 as ConsoleU64};

    // for ops see circuit/types/integers/{add_checked,add_wrapped}.rs

    // var + var
    #[test]
    fn add_checked_var_var() {
        let a = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(0u64));
        let b = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(1u64));
        let _candidate = &a + &b; // '+' on integers turns into a.add_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// add (checked) u64 private var with u64 private var");
        println!("{}", output);
    }

    // add constant 0
    #[test]
    fn add_checked_0_var() {
        let a = U64::<FormalCircuit>::new(Mode::Constant, ConsoleU64::zero());
        let b = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(1u64));
        let _candidate = &a + &b; // '+' on integers turns into a.add_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// add (checked) 0u64 constant with u64 private var");
        println!("{}", output);
    }

    // add constant 1
    #[test]
    fn add_checked_1_var() {
        let a = U64::<FormalCircuit>::new(Mode::Constant, ConsoleU64::new(1u64));
        let b = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(1u64));
        let _candidate = &a + &b; // '+' on integers turns into a.add_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// add (checked) 1u64 constant with u64 private var");
        println!("{}", output);
    }

    // add constant 1 in the other order
    #[test]
    fn add_checked_var_1() {
        let a = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(1u64));
        let b = U64::<FormalCircuit>::new(Mode::Constant, ConsoleU64::new(1u64));
        let _candidate = &a + &b; // '+' on integers turns into a.add_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// add (checked) u64 private var with 1u64 constant");
        println!("{}", output);
    }

    // Try adding a larger constant.  This is 2^64 - 2.
    // Note, this constant can also be made with ConsoleU64::from_str("18446744073709551614u64").unwrap());
    #[test]
    fn add_checked_N_var() {
        let a = U64::<FormalCircuit>::new(Mode::Constant, ConsoleU64::new(18446744073709551614u64));
        let b = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(1u64));
        let _candidate = &a + &b; // '+' on integers turns into a.add_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// add (checked) u64 private with u64 private ");
        println!("{}", output);
    }

    #[test]
    fn add_wrapped_var_var() {
        let a = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(0u64));
        let b = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(1u64));
        let _candidate = &a.add_wrapped(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// add (wrapped) u64 private with u64 private ");
        println!("{}", output);
    }

    // We don't need to do as many samples for add_wrapped, since it is simpler, but we do both directions of constant.
    #[test]
    fn add_wrapped_6_var() {
        let a = U64::<FormalCircuit>::new(Mode::Constant, ConsoleU64::new(6u64));
        let b = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(1u64));
        let _candidate = &a.add_wrapped(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// add (checked) u64 private with u64 private ");
        println!("{}", output);
    }

    #[test]
    fn add_wrapped_var_6() {
        let a = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(1u64));
        let b = U64::<FormalCircuit>::new(Mode::Constant, ConsoleU64::new(6u64));
        let _candidate = &a.add_wrapped(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// add (checked) u64 private with u64 private ");
        println!("{}", output);
    }

    // for ops see circuit/types/integers/{sub_checked,sub_wrapped}.rs

    // var - var
    #[test]
    fn sub_checked_var_var() {
        let a = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(0u64));
        let b = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(1u64));
        let _candidate = &a - &b; // '-' on integers turns into a.sub_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// sub (checked) u64 private var with u64 private var");
        println!("{}", output);
    }

    // sub constant 0
    #[test]
    fn sub_checked_0_var() {
        let a = U64::<FormalCircuit>::new(Mode::Constant, ConsoleU64::zero());
        let b = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(1u64));
        let _candidate = &a - &b; // '-' on integers turns into a.sub_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// sub (checked) 0u64 constant with u64 private var");
        println!("{}", output);
    }

    // sub constant 1
    #[test]
    fn sub_checked_1_var() {
        let a = U64::<FormalCircuit>::new(Mode::Constant, ConsoleU64::new(1u64));
        let b = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(1u64));
        let _candidate = &a - &b; // '-' on integers turns into a.sub_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// sub (checked) 1u64 constant with u64 private var");
        println!("{}", output);
    }

    // sub constant 1 in the other order
    #[test]
    fn sub_checked_var_1() {
        let a = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(1u64));
        let b = U64::<FormalCircuit>::new(Mode::Constant, ConsoleU64::new(1u64));
        let _candidate = &a - &b; // '-' on integers turns into a.sub_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// sub (checked) u64 private var with 1u64 constant");
        println!("{}", output);
    }

    // Try subing a larger constant.  This is 2^64 - 2.
    // Note, this constant can also be made with ConsoleU64::from_str("18446744073709551614u64").unwrap());
    #[test]
    fn sub_checked_N_var() {
        let a = U64::<FormalCircuit>::new(Mode::Constant, ConsoleU64::new(18446744073709551614u64));
        let b = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(1u64));
        let _candidate = &a - &b; // '-' on integers turns into a.sub_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// sub (checked) u64 private with u64 private ");
        println!("{}", output);
    }

    #[test]
    fn sub_wrapped_var_var() {
        let a = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(0u64));
        let b = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(1u64));
        let _candidate = &a.sub_wrapped(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// sub (wrapped) u64 private with u64 private ");
        println!("{}", output);
    }

    // We don't need to do as many samples for sub_wrapped, since it is simpler, but we do both directions of constant.
    #[test]
    fn sub_wrapped_6_var() {
        let a = U64::<FormalCircuit>::new(Mode::Constant, ConsoleU64::new(6u64));
        let b = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(1u64));
        let _candidate = &a.sub_wrapped(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// sub (checked) u64 private with u64 private ");
        println!("{}", output);
    }

    #[test]
    fn sub_wrapped_var_6() {
        let a = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(1u64));
        let b = U64::<FormalCircuit>::new(Mode::Constant, ConsoleU64::new(6u64));
        let _candidate = &a.sub_wrapped(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// sub (checked) u64 private with u64 private ");
        println!("{}", output);
    }

    // for ops see circuit/types/integers/{mul_checked,mul_wrapped}.rs

    // var * var
    #[test]
    fn mul_checked_var_var() {
        let a = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(0u64));
        let b = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(1u64));
        let _candidate = &a * &b; // '*' on integers turns into a.mul_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// mul (checked) u64 private var with u64 private var");
        println!("{}", output);
    }

    // mul constant 0
    #[test]
    fn mul_checked_0_var() {
        let a = U64::<FormalCircuit>::new(Mode::Constant, ConsoleU64::zero());
        let b = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(1u64));
        let _candidate = &a * &b; // '*' on integers turns into a.mul_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// mul (checked) 0u64 constant with u64 private var");
        println!("{}", output);
    }

    // mul constant 1
    #[test]
    fn mul_checked_1_var() {
        let a = U64::<FormalCircuit>::new(Mode::Constant, ConsoleU64::new(1u64));
        let b = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(1u64));
        let _candidate = &a * &b; // '*' on integers turns into a.mul_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// mul (checked) 1u64 constant with u64 private var");
        println!("{}", output);
    }

    // mul constant 1 in the other order
    #[test]
    fn mul_checked_var_1() {
        let a = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(1u64));
        let b = U64::<FormalCircuit>::new(Mode::Constant, ConsoleU64::new(1u64));
        let _candidate = &a * &b; // '*' on integers turns into a.mul_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// mul (checked) u64 private var with 1u64 constant");
        println!("{}", output);
    }

    // Try muling a larger constant.  This is 2^64 - 2.
    // Note, this constant can also be made with ConsoleU64::from_str("18446744073709551614u64").unwrap());
    #[test]
    fn mul_checked_N_var() {
        let a = U64::<FormalCircuit>::new(Mode::Constant, ConsoleU64::new(18446744073709551614u64));
        let b = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(1u64));
        let _candidate = &a * &b; // '*' on integers turns into a.mul_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// mul (checked) u64 private with u64 private ");
        println!("{}", output);
    }

    #[test]
    fn mul_wrapped_var_var() {
        let a = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(0u64));
        let b = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(1u64));
        let _candidate = &a.mul_wrapped(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// mul (wrapped) u64 private with u64 private ");
        println!("{}", output);
    }

    // We don't need to do as many samples for mul_wrapped, since it is simpler, but we do both directions of constant.
    #[test]
    fn mul_wrapped_6_var() {
        let a = U64::<FormalCircuit>::new(Mode::Constant, ConsoleU64::new(6u64));
        let b = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(1u64));
        let _candidate = &a.mul_wrapped(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// mul (checked) u64 private with u64 private ");
        println!("{}", output);
    }

    #[test]
    fn mul_wrapped_var_6() {
        let a = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(1u64));
        let b = U64::<FormalCircuit>::new(Mode::Constant, ConsoleU64::new(6u64));
        let _candidate = &a.mul_wrapped(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// mul (checked) u64 private with u64 private ");
        println!("{}", output);
    }

    // for ops see circuit/types/integers/{div_checked,div_wrapped}.rs
    // However, unsigned div (checked) and unsigned div.w (wrapped) are identical.
    // So we don't bother getting samples of div_wrapped.

    // var / var
    #[test]
    fn div_checked_var_var() {
        let a = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(0u64));
        let b = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(1u64));
        let _candidate = &a / &b; // '/' on integers turns into a.div_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// div (checked) u64 private var with u64 private var");
        println!("{}", output);
    }

    // div constant 0
    #[test]
    fn div_checked_0_var() {
        let a = U64::<FormalCircuit>::new(Mode::Constant, ConsoleU64::zero());
        let b = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(1u64));
        let _candidate = &a / &b; // '/' on integers turns into a.div_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// div (checked) 0u64 constant with u64 private var");
        println!("{}", output);
    }

    // div constant 1
    #[test]
    fn div_checked_1_var() {
        let a = U64::<FormalCircuit>::new(Mode::Constant, ConsoleU64::new(1u64));
        let b = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(1u64));
        let _candidate = &a / &b; // '/' on integers turns into a.div_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// div (checked) 1u64 constant with u64 private var");
        println!("{}", output);
    }

    // div constant 1 in the other order
    #[test]
    fn div_checked_var_1() {
        let a = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(1u64));
        let b = U64::<FormalCircuit>::new(Mode::Constant, ConsoleU64::new(1u64));
        let _candidate = &a / &b; // '/' on integers turns into a.div_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// div (checked) u64 private var with 1u64 constant");
        println!("{}", output);
    }

    // Try diving a larger constant.  This is 2^64 - 2.
    // Note, this constant can also be made with ConsoleU64::from_str("18446744073709551614u64").unwrap());
    #[test]
    fn div_checked_N_var() {
        let a = U64::<FormalCircuit>::new(Mode::Constant, ConsoleU64::new(18446744073709551614u64));
        let b = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(1u64));
        let _candidate = &a / &b; // '/' on integers turns into a.div_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// div. (checked) u64 private with u64 private ");
        println!("{}", output);
    }

    #[test]
    fn div_checked_var_N() {
        let a = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(1u64));
        let b = U64::<FormalCircuit>::new(Mode::Constant, ConsoleU64::new(18446744073709551614u64));
        let _candidate = &a / &b; // '/' on integers turns into a.div_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// div. (checked) u64 private with u64 private ");
        println!("{}", output);
    }

    // for ops see circuit/types/integers/{rem_checked,rem_wrapped}.rs
    // However, unsigned rem (checked) and unsigned rem.w (wrapped) are identical.
    // So we don't bother getting samples of rem_wrapped.

    // var % var
    #[test]
    fn rem_checked_var_var() {
        let a = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(0u64));
        let b = U64::<FormalCircuit>::new(Mode::Private, ConsoleU64::new(1u64));
        let _candidate = &a % &b; // '%' on integers turns into a.rem_checked(b)

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// rem (checked) u64 private var with u64 private var");
        println!("{}", output);
    }

    // If you want to try a signed op to take a look at it:
    /*
    #[test]
    fn add_checked_signed() {
        let a = I64::<FormalCircuit>::new(Mode::Private, ConsoleI64::new(0i64));
        let b = I64::<FormalCircuit>::new(Mode::Private, ConsoleI64::new(1i64));
        let _candidate = &a + &b;

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// add (checked) i64 private with i64 private ");
        println!("{}", output);
    }
     */
}
