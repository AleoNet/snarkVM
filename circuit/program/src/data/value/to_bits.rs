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

impl<A: Aleo> ToBits for Value<A, Plaintext<A>> {
    type Boolean = Boolean<A>;

    /// Returns this value as a list of **little-endian** bits.
    fn to_bits_le(&self) -> Vec<Self::Boolean> {
        let mut bits_le = match self {
            Self::Constant(..) => vec![Boolean::constant(false), Boolean::constant(false)],
            Self::Public(..) => vec![Boolean::constant(false), Boolean::constant(true)],
            Self::Private(..) => vec![Boolean::constant(true), Boolean::constant(false)],
            Self::Record(..) => vec![Boolean::constant(true), Boolean::constant(true)],
        };
        match self {
            Self::Constant(value) => bits_le.extend(value.to_bits_le()),
            Self::Public(value) => bits_le.extend(value.to_bits_le()),
            Self::Private(value) => bits_le.extend(value.to_bits_le()),
            Self::Record(value) => bits_le.extend(value.to_bits_le()),
        }
        bits_le
    }

    /// Returns this value as a list of **big-endian** bits.
    fn to_bits_be(&self) -> Vec<Self::Boolean> {
        let mut bits_be = match self {
            Self::Constant(..) => vec![Boolean::constant(false), Boolean::constant(false)],
            Self::Public(..) => vec![Boolean::constant(false), Boolean::constant(true)],
            Self::Private(..) => vec![Boolean::constant(true), Boolean::constant(false)],
            Self::Record(..) => vec![Boolean::constant(true), Boolean::constant(true)],
        };
        match self {
            Self::Constant(value) => bits_be.extend(value.to_bits_be()),
            Self::Public(value) => bits_be.extend(value.to_bits_be()),
            Self::Private(value) => bits_be.extend(value.to_bits_be()),
            Self::Record(value) => bits_be.extend(value.to_bits_be()),
        }
        bits_be
    }
}

impl<A: Aleo> ToBits for Value<A, Ciphertext<A>> {
    type Boolean = Boolean<A>;

    /// Returns this value as a list of **little-endian** bits.
    fn to_bits_le(&self) -> Vec<Self::Boolean> {
        let mut bits_le = match self {
            Self::Constant(..) => vec![Boolean::constant(false), Boolean::constant(false)],
            Self::Public(..) => vec![Boolean::constant(false), Boolean::constant(true)],
            Self::Private(..) => vec![Boolean::constant(true), Boolean::constant(false)],
            Self::Record(..) => vec![Boolean::constant(true), Boolean::constant(true)],
        };
        match self {
            Self::Constant(value) => bits_le.extend(value.to_bits_le()),
            Self::Public(value) => bits_le.extend(value.to_bits_le()),
            Self::Private(value) => bits_le.extend(value.to_bits_le()),
            Self::Record(value) => bits_le.extend(value.to_bits_le()),
        }
        bits_le
    }

    /// Returns this value as a list of **big-endian** bits.
    fn to_bits_be(&self) -> Vec<Self::Boolean> {
        let mut bits_be = match self {
            Self::Constant(..) => vec![Boolean::constant(false), Boolean::constant(false)],
            Self::Public(..) => vec![Boolean::constant(false), Boolean::constant(true)],
            Self::Private(..) => vec![Boolean::constant(true), Boolean::constant(false)],
            Self::Record(..) => vec![Boolean::constant(true), Boolean::constant(true)],
        };
        match self {
            Self::Constant(value) => bits_be.extend(value.to_bits_be()),
            Self::Public(value) => bits_be.extend(value.to_bits_be()),
            Self::Private(value) => bits_be.extend(value.to_bits_be()),
            Self::Record(value) => bits_be.extend(value.to_bits_be()),
        }
        bits_be
    }
}
