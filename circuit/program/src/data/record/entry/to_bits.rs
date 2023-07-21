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

impl<A: Aleo, T: Visibility<A>> ToBitsInto for Entry<A, T> {
    type Boolean = Boolean<A>;

    /// Returns this entry as a list of **little-endian** bits.
    fn to_bits_le_into(&self, vec: &mut Vec<Self::Boolean>) {
        match self {
            Self::Constant(..) => vec.extend_from_slice(&[Boolean::constant(false), Boolean::constant(false)]),
            Self::Public(..) => vec.extend_from_slice(&[Boolean::constant(false), Boolean::constant(true)]),
            Self::Private(..) => vec.extend_from_slice(&[Boolean::constant(true), Boolean::constant(false)]),
        };
        match self {
            Self::Constant(plaintext) => plaintext.to_bits_le_into(vec),
            Self::Public(plaintext) => plaintext.to_bits_le_into(vec),
            Self::Private(plaintext) => plaintext.to_bits_le_into(vec),
        }
    }

    /// Returns this entry as a list of **big-endian** bits.
    fn to_bits_be_into(&self, vec: &mut Vec<Self::Boolean>) {
        match self {
            Self::Constant(..) => vec.extend_from_slice(&[Boolean::constant(false), Boolean::constant(false)]),
            Self::Public(..) => vec.extend_from_slice(&[Boolean::constant(false), Boolean::constant(true)]),
            Self::Private(..) => vec.extend_from_slice(&[Boolean::constant(true), Boolean::constant(false)]),
        };
        match self {
            Self::Constant(plaintext) => plaintext.to_bits_be_into(vec),
            Self::Public(plaintext) => plaintext.to_bits_be_into(vec),
            Self::Private(plaintext) => plaintext.to_bits_be_into(vec),
        }
    }
}
