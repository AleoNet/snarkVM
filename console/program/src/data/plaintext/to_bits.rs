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

impl<N: Network> ToBits for Plaintext<N> {
    /// Returns this plaintext as a list of **little-endian** bits.
    fn to_bits_le(&self) -> Vec<bool> {
        match self {
            Self::Literal(literal, bits_le) => bits_le
                .get_or_init(|| {
                    let mut bits_le = vec![false, false]; // Variant bits.
                    bits_le.extend(literal.variant().to_bits_le());
                    bits_le.extend(literal.size_in_bits().to_bits_le());
                    bits_le.extend(literal.to_bits_le());
                    bits_le
                })
                .clone(),
            Self::Struct(struct_, bits_le) => bits_le
                .get_or_init(|| {
                    let mut bits_le = vec![false, true]; // Variant bits.
                    bits_le.extend(
                        u8::try_from(struct_.len())
                            .or_halt_with::<N>("Plaintext struct length exceeds u8::MAX")
                            .to_bits_le(),
                    );
                    for (identifier, value) in struct_ {
                        let value_bits = value.to_bits_le();
                        bits_le.extend(identifier.size_in_bits().to_bits_le());
                        bits_le.extend(identifier.to_bits_le());
                        bits_le.extend(
                            u16::try_from(value_bits.len())
                                .or_halt_with::<N>("Plaintext member exceeds u16::MAX bits")
                                .to_bits_le(),
                        );
                        bits_le.extend(value_bits);
                    }
                    bits_le
                })
                .clone(),
        }
    }

    /// Returns this plaintext as a list of **big-endian** bits.
    fn to_bits_be(&self) -> Vec<bool> {
        match self {
            Self::Literal(literal, bits_be) => bits_be
                .get_or_init(|| {
                    let mut bits_be = vec![false, false]; // Variant bits.
                    bits_be.extend(literal.variant().to_bits_be());
                    bits_be.extend(literal.size_in_bits().to_bits_be());
                    bits_be.extend(literal.to_bits_be());
                    bits_be
                })
                .clone(),
            Self::Struct(struct_, bits_be) => bits_be
                .get_or_init(|| {
                    let mut bits_be = vec![false, true]; // Variant bits.
                    bits_be.extend(
                        u8::try_from(struct_.len())
                            .or_halt_with::<N>("Plaintext struct length exceeds u8::MAX")
                            .to_bits_be(),
                    );
                    for (identifier, value) in struct_ {
                        let value_bits = value.to_bits_be();
                        bits_be.extend(identifier.size_in_bits().to_bits_be());
                        bits_be.extend(identifier.to_bits_be());
                        bits_be.extend(
                            u16::try_from(value_bits.len())
                                .or_halt_with::<N>("Plaintext member exceeds u16::MAX bits")
                                .to_bits_be(),
                        );
                        bits_be.extend(value_bits);
                    }
                    bits_be
                })
                .clone(),
        }
    }
}
