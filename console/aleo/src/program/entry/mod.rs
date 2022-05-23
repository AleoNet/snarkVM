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

mod helpers;
pub use helpers::*;

mod encrypt;
// mod to_bits;

use crate::{FromFields, Identifier, Literal, Network, ToFields};
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{FromBits, ToBits};

use anyhow::{bail, Result};
use core::ops::Deref;
use itertools::Itertools;
use once_cell::sync::OnceCell;

pub trait Visibility<N: Network>: ToBits + FromBits + ToFields + FromFields {
    /// Returns the number of field elements to encode `self`.
    fn size_in_fields(&self) -> usize;
}

/// An entry stored in program data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Entry<N: Network, Private: Visibility<N>> {
    /// A constant entry.
    Constant(Plaintext<N>),
    /// A publicly-visible entry.
    Public(Plaintext<N>),
    /// A private entry encrypted under the account owner's address.
    Private(Private),
}

impl<N: Network, Private: Visibility<N>> ToBits for Entry<N, Private> {
    /// Returns this entry as a list of **little-endian** bits.
    fn to_bits_le(&self) -> Vec<bool> {
        let mut bits_le = match self {
            Self::Constant(..) => vec![false, false],
            Self::Public(..) => vec![false, true],
            Self::Private(..) => vec![true, false],
        };
        match self {
            Self::Constant(entry) => bits_le.extend(entry.to_bits_le()),
            Self::Public(entry) => bits_le.extend(entry.to_bits_le()),
            Self::Private(entry) => bits_le.extend(entry.to_bits_le()),
        }
        bits_le
    }

    /// Returns this entry as a list of **big-endian** bits.
    fn to_bits_be(&self) -> Vec<bool> {
        let mut bits_be = match self {
            Self::Constant(..) => vec![false, false],
            Self::Public(..) => vec![false, true],
            Self::Private(..) => vec![true, false],
        };
        match self {
            Self::Constant(entry) => bits_be.extend(entry.to_bits_be()),
            Self::Public(entry) => bits_be.extend(entry.to_bits_be()),
            Self::Private(entry) => bits_be.extend(entry.to_bits_be()),
        }
        bits_be
    }
}

// impl<N: Network, Literal: EntryMode<N>>> Entry<N, Literal> {
//     // /// Returns the recursive depth of this entry.
//     // /// Note: Once `generic_const_exprs` is stabilized, this can be replaced with `const DEPTH: u8`.
//     // fn depth(&self, counter: usize) -> usize {
//     //     match self {
//     //         Self::Literal(..) => 1,
//     //         Self::Composite(composite) => {
//     //             // Determine the maximum depth of the composite.
//     //             let max_depth = composite.iter().map(|(_, entry)| entry.depth(counter)).fold(0, |a, b| a.max(b));
//     //             // Add `1` to the depth of the member with the largest depth.
//     //             max_depth.saturating_add(1)
//     //         }
//     //     }
//     // }
// }
