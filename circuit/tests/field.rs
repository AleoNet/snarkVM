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

//! This test file will output JSON R1CS files for field gadgets in `circuits/types/field/`
//!
//! [Run all tests]: `cargo test -- --show-output`
//!
//! [Run a single test]: `cargo test field::add -- --show-output`
//!

extern crate snarkvm_circuit;

#[cfg(test)]
mod field {
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
    use snarkvm_circuit_types::{Compare, DivUnchecked, Double, Equal, Field, Pow, Square, Ternary};
    use snarkvm_console_types_field::{Field as ConsoleField, One, Zero};
    use std::ops::{BitAnd, BitOr};

    #[test]
    fn add() {
        // no constraints
        let a = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::zero());
        let b = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::one());
        let _candidate = &a + &b;

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// add");
        println!("{}", output);
    }

    #[test]
    fn compare() {
        let a = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::zero());
        let b = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::one());
        let _candidate = a.is_less_than(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// compare");
        println!("{}", output);
    }

    #[test]
    fn div() {
        let a = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::zero());
        let b = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::one());
        let _candidate = &a / &b;

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// div");
        println!("{}", output);
    }

    #[test]
    fn div_unchecked() {
        let a = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::zero());
        let b = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::one());
        let _candidate = a.div_unchecked(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// div_unchecked");
        println!("{}", output);
    }

    #[test]
    fn double() {
        // no constraints
        let a = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::zero());
        let _candidate = a.double();

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// double");
        println!("{}", output);
    }

    #[test]
    fn equal() {
        let a = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::zero());
        let b = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::one());
        let _candidate = a.is_not_equal(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// equal");
        println!("{}", output);
    }

    #[test]
    fn from_bits_le() {
        let mut bits = vec![];
        for _i in 0..256 {
            bits.push(Boolean::<FormalCircuit>::new(Mode::Private, false));
        }
        let _candidate = Field::<FormalCircuit>::from_bits_le(&bits);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// from_bits_le");
        println!("{}", output);
    }

    #[test]
    fn from_bits_le_diff_const() {
        let mut bits = vec![];
        for _i in 0..10 {
            bits.push(Boolean::<FormalCircuit>::new(Mode::Private, false));
        }
        let constant = vec![true, true, true, false, false, false, true, true, false, true];
        let is_lte = !constant.iter().zip_eq(bits).fold(Boolean::constant(false), |rest_is_less, (this, that)| {
            if *this { that.bitand(&rest_is_less) } else { that.bitor(&rest_is_less) }
        });
        FormalCircuit::assert(is_lte);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// from_bits_le");
        println!("{}", output);
    }

    #[test]
    fn inverse() {
        let a = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::zero());
        let _candidate = a.inverse();

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// inverse");
        println!("{}", output);
    }

    #[test]
    fn mul() {
        let a = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::zero());
        let b = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::one());
        let _candidate = &a * &b;

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// mul");
        println!("{}", output);
    }

    #[test]
    fn neg() {
        // no constraints
        let a = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::zero());
        let _candidate = -&a;

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// neg");
        println!("{}", output);
    }

    #[test]
    fn pow10() {  // variable field to the power of constant 10
        let one = ConsoleField::one();
        let two = one + one;
        let four = two + two;
        let eight = four + four;
        let ten = eight + two;

        let a = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::zero());
        let b = Field::<FormalCircuit>::new(Mode::Constant, ten);

        let _candidate = a.pow(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// pow10");
        println!("{}", output);
    }

    #[test]
    fn c7237005577332262213973186563042994240829374041602535252466099000494570602495pow() {  // constant 2^252 - 1 to the power of a variable field

        let two_to_the_252_minus_1 = ConsoleField::from_str("7237005577332262213973186563042994240829374041602535252466099000494570602495field");

        let a = Field::<FormalCircuit>::new(Mode::Constant, two_to_the_252_minus_1.unwrap());
        let b = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::one());
        let _candidate = a.pow(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// c7237005577332262213973186563042994240829374041602535252466099000494570602495pow");
        println!("{}", output);
    }

    #[test]
    fn c15pow() {  // constant 15 to the power of a variable field
        let fifteen = ConsoleField::from_str("15field");

        let a = Field::<FormalCircuit>::new(Mode::Constant, fifteen.unwrap());
        let b = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::one());
        let _candidate = a.pow(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// c15pow");  // 15field ** field
        println!("{}", output);
    }

    #[test]
    fn c11pow() {  // constant 11 to the power of a variable field
        let eleven = ConsoleField::from_str("11field");

        let a = Field::<FormalCircuit>::new(Mode::Constant, eleven.unwrap());
        let b = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::one());
        let _candidate = a.pow(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// c11pow");  // 11field ** field
        println!("{}", output);
    }

    #[test]
    fn c6pow() {  // constant 6 to the power of a variable field
        let one = ConsoleField::one();
        let two = one + one;
        let four = two + two;
        let six = four + two;

        let a = Field::<FormalCircuit>::new(Mode::Constant, six);
        let b = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::one());
        let _candidate = a.pow(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// c6pow");  // 6field ** field
        println!("{}", output);
    }

    #[test]
    fn c1pow() {  // constant 1 to the power of a variable field
        let one = ConsoleField::one();

        let a = Field::<FormalCircuit>::new(Mode::Constant, one);
        let b = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::one());
        let _candidate = a.pow(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// c1pow");  // 1field ** field
        println!("{}", output);
    }

    #[test]
    fn c0pow() {  // constant 0 to the power of a variable field

        let a = Field::<FormalCircuit>::new(Mode::Constant, ConsoleField::zero());
        let b = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::one());
        let _candidate = a.pow(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// c0pow");  // 0field ** field
        println!("{}", output);
    }

    #[test]
    fn pow() {
        let a = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::zero());
        let b = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::one());
        let _candidate = a.pow(&b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// pow");
        println!("{}", output);
    }

    #[test]
    fn square() {
        // no constraints
        let a = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::zero());
        let _candidate = a.square();

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// square");
        println!("{}", output);
    }

    #[test]
    fn square_root() {
        // no constraints
        let a = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::zero());
        let _candidate = a.square_root();

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// square_root");
        println!("{}", output);
    }

    #[test]
    fn sub() {
        // no constraints
        let a = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::zero());
        let b = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::one());
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
        let a = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::zero());
        let b = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::one());
        let _candidate = Field::ternary(&condition, &a, &b);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// ternary");
        println!("{}", output);
    }

    #[test]
    fn to_bits_le() {
        let a = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::zero());
        let _candidate = a.to_bits_le();

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// to bits le");
        println!("{}", output);
    }
}
