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

impl<N: Network> Literal<N> {
    /// Initializes a new literal from a list of little-endian bits *without* trailing zeros.
    pub fn from_bits_le(variant: u8, bits_le: &[bool]) -> Result<Self> {
        let literal = bits_le;
        let literal = match variant {
            0 => Literal::Address(Address::from_group(N::affine_from_x_coordinate(N::field_from_bits_le(literal)?)?)),
            1 => match bits_le.len() {
                1 => Literal::Boolean(literal[0]),
                _ => bail!("Expected a boolean literal, but found a list of {} bits.", bits_le.len()),
            },
            2 => Literal::Field(N::field_from_bits_le(literal)?),
            3 => Literal::Group(N::affine_from_x_coordinate(N::field_from_bits_le(literal)?)?),
            4 => Literal::I8(i8::from_bits_le(literal)?),
            5 => Literal::I16(i16::from_bits_le(literal)?),
            6 => Literal::I32(i32::from_bits_le(literal)?),
            7 => Literal::I64(i64::from_bits_le(literal)?),
            8 => Literal::I128(i128::from_bits_le(literal)?),
            9 => Literal::U8(u8::from_bits_le(literal)?),
            10 => Literal::U16(u16::from_bits_le(literal)?),
            11 => Literal::U32(u32::from_bits_le(literal)?),
            12 => Literal::U64(u64::from_bits_le(literal)?),
            13 => Literal::U128(u128::from_bits_le(literal)?),
            14 => Literal::Scalar(N::scalar_from_bits_le(literal)?),
            15 => {
                let buffer = Vec::<u8>::from_bits_be(literal)?;
                match buffer.len() <= N::NUM_STRING_BYTES as usize {
                    true => Self::String(String::from_utf8(buffer).map_err(|e| error(format!("{e}")))?),
                    false => bail!("String literal exceeds maximum length of {} bytes.", N::NUM_STRING_BYTES),
                }
            }
            16.. => bail!("Failed to initialize literal variant {} from bits (LE)", variant),
        };
        Ok(literal)
    }

    /// Initializes a new literal from a list of big-endian bits *without* leading zeros.
    pub fn from_bits_be(variant: u8, bits_be: &[bool]) -> Result<Self> {
        let literal = bits_be;
        let literal = match variant {
            0 => Literal::Address(Address::from_group(N::affine_from_x_coordinate(N::field_from_bits_be(literal)?)?)),
            1 => match bits_be.len() {
                1 => Literal::Boolean(literal[0]),
                _ => bail!("Expected a boolean literal, but found a list of {} bits.", bits_be.len()),
            },
            2 => Literal::Field(N::field_from_bits_be(literal)?),
            3 => Literal::Group(N::affine_from_x_coordinate(N::field_from_bits_be(literal)?)?),
            4 => Literal::I8(i8::from_bits_be(literal)?),
            5 => Literal::I16(i16::from_bits_be(literal)?),
            6 => Literal::I32(i32::from_bits_be(literal)?),
            7 => Literal::I64(i64::from_bits_be(literal)?),
            8 => Literal::I128(i128::from_bits_be(literal)?),
            9 => Literal::U8(u8::from_bits_be(literal)?),
            10 => Literal::U16(u16::from_bits_be(literal)?),
            11 => Literal::U32(u32::from_bits_be(literal)?),
            12 => Literal::U64(u64::from_bits_be(literal)?),
            13 => Literal::U128(u128::from_bits_be(literal)?),
            14 => Literal::Scalar(N::scalar_from_bits_be(literal)?),
            15 => {
                let buffer = Vec::<u8>::from_bits_be(literal)?;
                match buffer.len() <= N::NUM_STRING_BYTES as usize {
                    true => Self::String(String::from_utf8(buffer).map_err(|e| error(format!("{e}")))?),
                    false => bail!("String literal exceeds maximum length of {} bytes.", N::NUM_STRING_BYTES),
                }
            }
            16.. => bail!("Failed to initialize literal variant {} from bits (BE))", variant),
        };
        Ok(literal)
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;
//     use snarkvm_circuits_environment::Circuit;
//     use snarkvm_utilities::{rand::Rng, test_rng, UniformRand};
//
//     const ITERATIONS: u32 = 1000;
//
//     fn check_serialization(expected: Literal<Circuit>) {
//         // Success cases.
//         assert_eq!(expected.eject_value(), Literal::from_bits_le(&expected.to_bits_le()).eject_value());
//         assert_eq!(expected.eject_value(), Literal::from_bits_be(&expected.to_bits_be()).eject_value());
//
//         // Failure cases.
//         assert!(std::panic::catch_unwind(|| Literal::from_bits_le(&expected.to_bits_be()).eject_value()).is_err());
//         Circuit::reset();
//         assert!(std::panic::catch_unwind(|| Literal::from_bits_be(&expected.to_bits_le()).eject_value()).is_err());
//         Circuit::reset();
//     }
//
//     fn run_serialization_test(mode: Mode) {
//         let rng = &mut test_rng();
//
//         for _ in 0..ITERATIONS {
//             // // Address
//             // check_serialization(Literal::<Circuit>::Address(Address::new(mode, UniformRand::rand(rng))));
//             // Boolean
//             check_serialization(Literal::<Circuit>::Boolean(Boolean::new(mode, UniformRand::rand(rng))));
//             // Field
//             check_serialization(Literal::<Circuit>::Field(Field::new(mode, UniformRand::rand(rng))));
//             // Group
//             check_serialization(Literal::<Circuit>::Group(Group::new(mode, UniformRand::rand(rng))));
//             // I8
//             check_serialization(Literal::<Circuit>::I8(I8::new(mode, UniformRand::rand(rng))));
//             // I16
//             check_serialization(Literal::<Circuit>::I16(I16::new(mode, UniformRand::rand(rng))));
//             // I32
//             check_serialization(Literal::<Circuit>::I32(I32::new(mode, UniformRand::rand(rng))));
//             // I64
//             check_serialization(Literal::<Circuit>::I64(I64::new(mode, UniformRand::rand(rng))));
//             // I128
//             check_serialization(Literal::<Circuit>::I128(I128::new(mode, UniformRand::rand(rng))));
//             // U8
//             check_serialization(Literal::<Circuit>::U8(U8::new(mode, UniformRand::rand(rng))));
//             // U16
//             check_serialization(Literal::<Circuit>::U16(U16::new(mode, UniformRand::rand(rng))));
//             // U32
//             check_serialization(Literal::<Circuit>::U32(U32::new(mode, UniformRand::rand(rng))));
//             // U64
//             check_serialization(Literal::<Circuit>::U64(U64::new(mode, UniformRand::rand(rng))));
//             // U128
//             check_serialization(Literal::<Circuit>::U128(U128::new(mode, UniformRand::rand(rng))));
//             // Scalar
//             check_serialization(Literal::<Circuit>::Scalar(Scalar::new(mode, UniformRand::rand(rng))));
//             // String
//             // Sample a random string. Take 1/4th to ensure we fit for all code points.
//             let range = 0..rng.gen_range(0..Circuit::NUM_STRING_BYTES / 4);
//             let string: String = range.map(|_| rng.gen::<char>()).collect();
//             check_serialization(Literal::<Circuit>::String(StringType::new(mode, string)));
//         }
//     }
//
//     #[test]
//     fn test_serialization_constant() {
//         run_serialization_test(Mode::Constant);
//     }
//
//     #[test]
//     fn test_serialization_public() {
//         run_serialization_test(Mode::Public);
//     }
//
//     #[test]
//     fn test_serialization_private() {
//         run_serialization_test(Mode::Private);
//     }
// }
