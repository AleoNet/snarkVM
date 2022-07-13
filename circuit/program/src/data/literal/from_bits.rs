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

use super::*;

impl<A: Aleo> Literal<A> {
    /// Initializes a new literal from a list of little-endian bits *without* trailing zeros.
    pub fn from_bits_le(variant: &U8<A>, bits_le: &[Boolean<A>]) -> Self {
        let literal = bits_le;
        match *variant.eject_value() {
            0 => Literal::Address(Address::from_bits_le(literal)),
            1 => Literal::Boolean(Boolean::from_bits_le(literal)),
            2 => Literal::Field(Field::from_bits_le(literal)),
            3 => Literal::Group(Group::from_bits_le(literal)),
            4 => Literal::I8(I8::from_bits_le(literal)),
            5 => Literal::I16(I16::from_bits_le(literal)),
            6 => Literal::I32(I32::from_bits_le(literal)),
            7 => Literal::I64(I64::from_bits_le(literal)),
            8 => Literal::I128(I128::from_bits_le(literal)),
            9 => Literal::U8(U8::from_bits_le(literal)),
            10 => Literal::U16(U16::from_bits_le(literal)),
            11 => Literal::U32(U32::from_bits_le(literal)),
            12 => Literal::U64(U64::from_bits_le(literal)),
            13 => Literal::U128(U128::from_bits_le(literal)),
            14 => Literal::Scalar(Scalar::from_bits_le(literal)),
            15 => Literal::String(StringType::from_bits_le(literal)),
            16.. => A::halt(format!("Failed to initialize literal variant {} from bits (LE)", variant.eject_value())),
        }
    }

    /// Initializes a new literal from a list of big-endian bits *without* leading zeros.
    pub fn from_bits_be(variant: &U8<A>, bits_be: &[Boolean<A>]) -> Self {
        let literal = bits_be;
        match *variant.eject_value() {
            0 => Literal::Address(Address::from_bits_be(literal)),
            1 => Literal::Boolean(Boolean::from_bits_be(literal)),
            2 => Literal::Field(Field::from_bits_be(literal)),
            3 => Literal::Group(Group::from_bits_be(literal)),
            4 => Literal::I8(I8::from_bits_be(literal)),
            5 => Literal::I16(I16::from_bits_be(literal)),
            6 => Literal::I32(I32::from_bits_be(literal)),
            7 => Literal::I64(I64::from_bits_be(literal)),
            8 => Literal::I128(I128::from_bits_be(literal)),
            9 => Literal::U8(U8::from_bits_be(literal)),
            10 => Literal::U16(U16::from_bits_be(literal)),
            11 => Literal::U32(U32::from_bits_be(literal)),
            12 => Literal::U64(U64::from_bits_be(literal)),
            13 => Literal::U128(U128::from_bits_be(literal)),
            14 => Literal::Scalar(Scalar::from_bits_be(literal)),
            15 => Literal::String(StringType::from_bits_be(literal)),
            16.. => A::halt(format!("Failed to initialize literal variant {} from bits (BE))", variant.eject_value())),
        }
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use crate::Circuit;
    use console::{test_rng, Rng, Uniform};

    const ITERATIONS: u32 = 1000;

    fn check_serialization(expected: Literal<Circuit>) {
        // Success cases.
        assert_eq!(
            expected.eject_value(),
            Literal::from_bits_le(&expected.variant(), &expected.to_bits_le()).eject_value()
        );
        assert_eq!(
            expected.eject_value(),
            Literal::from_bits_be(&expected.variant(), &expected.to_bits_be()).eject_value()
        );

        // // Failure cases.
        // assert!(std::panic::catch_unwind(|| Literal::from_bits_le(&expected.variant(), &expected.to_bits_be()).eject_value()).is_err());
        // Circuit::reset();
        // assert!(std::panic::catch_unwind(|| Literal::from_bits_be(&expected.variant(), &expected.to_bits_le()).eject_value()).is_err());
        Circuit::reset();
    }

    fn run_serialization_test(mode: Mode) {
        let rng = &mut test_rng();

        for _ in 0..ITERATIONS {
            // Address
            check_serialization(Literal::<Circuit>::Address(Address::new(
                mode,
                console::Address::new(Uniform::rand(rng)),
            )));
            // Boolean
            check_serialization(Literal::<Circuit>::Boolean(Boolean::new(mode, Uniform::rand(rng))));
            // Field
            check_serialization(Literal::<Circuit>::Field(Field::new(mode, Uniform::rand(rng))));
            // Group
            check_serialization(Literal::<Circuit>::Group(Group::new(mode, Uniform::rand(rng))));
            // I8
            check_serialization(Literal::<Circuit>::I8(I8::new(mode, Uniform::rand(rng))));
            // I16
            check_serialization(Literal::<Circuit>::I16(I16::new(mode, Uniform::rand(rng))));
            // I32
            check_serialization(Literal::<Circuit>::I32(I32::new(mode, Uniform::rand(rng))));
            // I64
            check_serialization(Literal::<Circuit>::I64(I64::new(mode, Uniform::rand(rng))));
            // I128
            check_serialization(Literal::<Circuit>::I128(I128::new(mode, Uniform::rand(rng))));
            // U8
            check_serialization(Literal::<Circuit>::U8(U8::new(mode, Uniform::rand(rng))));
            // U16
            check_serialization(Literal::<Circuit>::U16(U16::new(mode, Uniform::rand(rng))));
            // U32
            check_serialization(Literal::<Circuit>::U32(U32::new(mode, Uniform::rand(rng))));
            // U64
            check_serialization(Literal::<Circuit>::U64(U64::new(mode, Uniform::rand(rng))));
            // U128
            check_serialization(Literal::<Circuit>::U128(U128::new(mode, Uniform::rand(rng))));
            // Scalar
            check_serialization(Literal::<Circuit>::Scalar(Scalar::new(mode, Uniform::rand(rng))));
            // String
            // Sample a random string. Take 1/4th to ensure we fit for all code points.
            let range = 0..rng.gen_range(0..Circuit::NUM_STRING_BYTES / 4);
            let string: String = range.map(|_| rng.gen::<char>()).collect();
            check_serialization(Literal::<Circuit>::String(StringType::new(mode, console::StringType::new(&string))));
        }
    }

    #[test]
    fn test_serialization_constant() {
        run_serialization_test(Mode::Constant);
    }

    #[test]
    fn test_serialization_public() {
        run_serialization_test(Mode::Public);
    }

    #[test]
    fn test_serialization_private() {
        run_serialization_test(Mode::Private);
    }
}
