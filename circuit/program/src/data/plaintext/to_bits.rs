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

use super::*;
use snarkvm_circuit_types::{U32, U64};

impl<A: Aleo> ToBits for Plaintext<A> {
    type Boolean = Boolean<A>;

    /// Returns this plaintext as a list of **little-endian** bits.
    fn to_bits_le(&self) -> Vec<Boolean<A>> {
        match self {
            Self::Literal(literal, bits_le) => bits_le
                .get_or_init(|| {
                    let mut bits_le = vec![Boolean::constant(false), Boolean::constant(false)]; // Variant bit.
                    bits_le.extend(literal.variant().to_bits_le());
                    bits_le.extend(literal.size_in_bits().to_bits_le());
                    bits_le.extend(literal.to_bits_le());
                    bits_le
                })
                .clone(),
            Self::Struct(members, bits_le) => bits_le
                .get_or_init(|| {
                    let mut bits_le = vec![Boolean::constant(false), Boolean::constant(true)]; // Variant bit.
                    bits_le.extend(U8::constant(console::U8::new(members.len() as u8)).to_bits_le());
                    for (identifier, value) in members {
                        let value_bits = value.to_bits_le();
                        bits_le.extend(identifier.size_in_bits().to_bits_le());
                        bits_le.extend(identifier.to_bits_le());
                        bits_le.extend(U16::constant(console::U16::new(value_bits.len() as u16)).to_bits_le());
                        bits_le.extend(value_bits);
                    }
                    bits_le
                })
                .clone(),
            Self::Array(array, bits_le) => bits_le
                .get_or_init(|| {
                    let mut bits_le = vec![Boolean::constant(true), Boolean::constant(false)]; // Variant bits.
                    bits_le.extend(U32::constant(console::U32::new(array.len() as u32)).to_bits_le());
                    for value in array {
                        let value_bits = value.to_bits_le();
                        bits_le.extend(U64::constant(console::U64::new(value_bits.len() as u64)).to_bits_le());
                        bits_le.extend(value_bits);
                    }
                    bits_le
                })
                .clone(),
        }
    }

    /// Returns this plaintext as a list of **big-endian** bits.
    fn to_bits_be(&self) -> Vec<Boolean<A>> {
        match self {
            Self::Literal(literal, bits_be) => bits_be
                .get_or_init(|| {
                    let mut bits_be = vec![Boolean::constant(false), Boolean::constant(false)]; // Variant bit.
                    bits_be.extend(literal.variant().to_bits_be());
                    bits_be.extend(literal.size_in_bits().to_bits_be());
                    bits_be.extend(literal.to_bits_be());
                    bits_be
                })
                .clone(),
            Self::Struct(members, bits_be) => bits_be
                .get_or_init(|| {
                    let mut bits_be = vec![Boolean::constant(false), Boolean::constant(true)]; // Variant bit.
                    bits_be.extend(U8::constant(console::U8::new(members.len() as u8)).to_bits_be());
                    for (identifier, value) in members {
                        let value_bits = value.to_bits_be();
                        bits_be.extend(identifier.size_in_bits().to_bits_be());
                        bits_be.extend(identifier.to_bits_be());
                        bits_be.extend(U16::constant(console::U16::new(value_bits.len() as u16)).to_bits_be());
                        bits_be.extend(value_bits);
                    }
                    bits_be
                })
                .clone(),
            Self::Array(array, bits_be) => bits_be
                .get_or_init(|| {
                    let mut bits_be = vec![Boolean::constant(true), Boolean::constant(false)]; // Variant bits.
                    bits_be.extend(U32::constant(console::U32::new(array.len() as u32)).to_bits_be());
                    for value in array {
                        let value_bits = value.to_bits_be();
                        bits_be.extend(U64::constant(console::U64::new(value_bits.len() as u64)).to_bits_be());
                        bits_be.extend(value_bits);
                    }
                    bits_be
                })
                .clone(),
        }
    }
}
