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

impl<A: Aleo> ToBits for Plaintext<A> {
    type Boolean = Boolean<A>;

    /// Returns this plaintext as a list of **little-endian** bits.
    fn write_bits_le(&self, vec: &mut Vec<Boolean<A>>) {
        match self {
            Self::Literal(literal, bits_le) => vec.extend_from_slice(bits_le.get_or_init(|| {
                let mut bits = vec![Boolean::constant(false), Boolean::constant(false)]; // Variant bit.
                literal.variant().write_bits_le(&mut bits);
                literal.size_in_bits().write_bits_le(&mut bits);
                literal.write_bits_le(&mut bits);
                bits
            })),
            Self::Struct(members, bits_le) => vec.extend_from_slice(bits_le.get_or_init(|| {
                let mut bits = vec![Boolean::constant(false), Boolean::constant(true)]; // Variant bit.
                U8::constant(console::U8::new(members.len() as u8)).write_bits_le(&mut bits);
                for (identifier, value) in members {
                    let value_bits = value.to_bits_le();
                    identifier.size_in_bits().write_bits_le(&mut bits);
                    identifier.write_bits_le(&mut bits);
                    U16::constant(console::U16::new(value_bits.len() as u16)).write_bits_le(&mut bits);
                    bits.extend_from_slice(&value_bits);
                }
                bits
            })),
        };
    }

    /// Returns this plaintext as a list of **big-endian** bits.
    fn write_bits_be(&self, vec: &mut Vec<Boolean<A>>) {
        match self {
            Self::Literal(literal, bits_be) => vec.extend_from_slice(bits_be.get_or_init(|| {
                let mut bits = vec![Boolean::constant(false), Boolean::constant(false)]; // Variant bit.
                literal.variant().write_bits_le(&mut bits);
                literal.size_in_bits().write_bits_le(&mut bits);
                literal.write_bits_le(&mut bits);
                bits
            })),
            Self::Struct(members, bits_be) => vec.extend_from_slice(bits_be.get_or_init(|| {
                let mut bits = vec![Boolean::constant(false), Boolean::constant(true)]; // Variant bit.
                U8::constant(console::U8::new(members.len() as u8)).write_bits_be(&mut bits);
                for (identifier, value) in members {
                    let value_bits = value.to_bits_be();
                    identifier.size_in_bits().write_bits_be(&mut bits);
                    identifier.write_bits_be(&mut bits);
                    U16::constant(console::U16::new(value_bits.len() as u16)).write_bits_be(&mut bits);
                    bits.extend_from_slice(&value_bits);
                }
                bits
            })),
        };
    }
}
