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

impl<A: Aleo> ToBitsInto for Plaintext<A> {
    type Boolean = Boolean<A>;

    /// Returns this plaintext as a list of **little-endian** bits.
    fn to_bits_le_into(&self, vec: &mut Vec<Self::Boolean>) {
        match self {
            Self::Literal(literal, bits_le) => vec.extend_from_slice(bits_le.get_or_init(|| {
                let mut bits_le = vec![Boolean::constant(false), Boolean::constant(false)]; // Variant bit.
                literal.variant().to_bits_le_into(&mut bits_le);
                literal.size_in_bits().to_bits_le_into(&mut bits_le);
                literal.to_bits_le_into(&mut bits_le);
                bits_le
            })),
            Self::Struct(members, bits_le) => vec.extend_from_slice(bits_le.get_or_init(|| {
                let mut bits_le = vec![Boolean::constant(false), Boolean::constant(true)]; // Variant bit.
                U8::constant(console::U8::new(members.len() as u8)).to_bits_le_into(&mut bits_le);
                for (identifier, value) in members {
                    let value_bits = value.to_bits_le();
                    identifier.size_in_bits().to_bits_le_into(&mut bits_le);
                    identifier.to_bits_le_into(&mut bits_le);
                    U16::constant(console::U16::new(value_bits.len() as u16)).to_bits_le_into(&mut bits_le);
                    bits_le.extend_from_slice(&value_bits);
                }
                bits_le
            })),
        }
    }

    /// Returns this plaintext as a list of **big-endian** bits.
    fn to_bits_be_into(&self, vec: &mut Vec<Self::Boolean>) {
        match self {
            Self::Literal(literal, bits_be) => vec.extend_from_slice(bits_be.get_or_init(|| {
                let mut bits_be = vec![Boolean::constant(false), Boolean::constant(false)]; // Variant bit.
                literal.variant().to_bits_be_into(&mut bits_be);
                literal.size_in_bits().to_bits_be_into(&mut bits_be);
                literal.to_bits_be_into(&mut bits_be);
                bits_be
            })),
            Self::Struct(members, bits_be) => vec.extend_from_slice(bits_be.get_or_init(|| {
                let mut bits_be = vec![Boolean::constant(false), Boolean::constant(true)]; // Variant bit.
                U8::constant(console::U8::new(members.len() as u8)).to_bits_be_into(&mut bits_be);
                for (identifier, value) in members {
                    let value_bits = value.to_bits_be();
                    identifier.size_in_bits().to_bits_be_into(&mut bits_be);
                    identifier.to_bits_be_into(&mut bits_be);
                    U16::constant(console::U16::new(value_bits.len() as u16)).to_bits_be_into(&mut bits_be);
                    bits_be.extend_from_slice(&value_bits);
                }
                bits_be
            })),
        }
    }
}
