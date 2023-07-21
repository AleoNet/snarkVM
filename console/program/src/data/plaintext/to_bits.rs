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

use snarkvm_utilities::ToBitsInto;

impl<N: Network> ToBitsInto for Plaintext<N> {
    /// Returns this plaintext as a list of **little-endian** bits.
    fn to_bits_le_into(&self, vec: &mut Vec<bool>) {
        match self {
            Self::Literal(literal, bits_le) => vec.extend_from_slice(bits_le.get_or_init(|| {
                let mut bits_le = vec![false, false]; // Variant bits.
                literal.variant().to_bits_le_into(&mut bits_le);
                literal.size_in_bits().to_bits_le_into(&mut bits_le);
                literal.to_bits_le_into(&mut bits_le);
                bits_le
            })),
            Self::Struct(struct_, bits_le) => vec.extend_from_slice(bits_le.get_or_init(|| {
                let mut bits_le = vec![false, true]; // Variant bits.
                u8::try_from(struct_.len())
                    .or_halt_with::<N>("Plaintext struct length exceeds u8::MAX")
                    .to_bits_le_into(&mut bits_le);
                for (identifier, value) in struct_ {
                    let value_bits = value.to_bits_le();
                    identifier.size_in_bits().to_bits_le_into(&mut bits_le);
                    identifier.to_bits_le_into(&mut bits_le);
                    u16::try_from(value_bits.len())
                        .or_halt_with::<N>("Plaintext member exceeds u16::MAX bits")
                        .to_bits_le_into(&mut bits_le);
                    bits_le.extend_from_slice(&value_bits);
                }
                bits_le
            })),
        }
    }

    /// Returns this plaintext as a list of **big-endian** bits.
    fn to_bits_be_into(&self, vec: &mut Vec<bool>) {
        match self {
            Self::Literal(literal, bits_be) => vec.extend_from_slice(bits_be.get_or_init(|| {
                let mut bits_be = vec![false, false]; // Variant bits.
                literal.variant().to_bits_be_into(&mut bits_be);
                literal.size_in_bits().to_bits_be_into(&mut bits_be);
                literal.to_bits_be_into(&mut bits_be);
                bits_be
            })),
            Self::Struct(struct_, bits_be) => vec.extend_from_slice(bits_be.get_or_init(|| {
                let mut bits_be = vec![false, true]; // Variant bits.
                u8::try_from(struct_.len())
                    .or_halt_with::<N>("Plaintext struct length exceeds u8::MAX")
                    .to_bits_be_into(&mut bits_be);
                for (identifier, value) in struct_ {
                    let value_bits = value.to_bits_be();
                    identifier.size_in_bits().to_bits_be_into(&mut bits_be);
                    identifier.to_bits_be_into(&mut bits_be);
                    u16::try_from(value_bits.len())
                        .or_halt_with::<N>("Plaintext member exceeds u16::MAX bits")
                        .to_bits_be_into(&mut bits_be);
                    bits_be.extend_from_slice(&value_bits);
                }
                bits_be
            })),
        }
    }
}
