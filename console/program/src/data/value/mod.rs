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

mod decrypt;
mod encrypt;
mod num_randomizers;
mod to_bits;
mod to_plaintext;

use crate::{Ciphertext, Plaintext, Visibility};
use snarkvm_console_network::Network;
use snarkvm_console_types::prelude::*;

/// A value stored in program data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value<N: Network, Private: Visibility<N>> {
    /// A constant value.
    Constant(Plaintext<N>),
    /// A publicly-visible value.
    Public(Plaintext<N>),
    /// A private value encrypted under the account owner's address.
    Private(Private),
}

// impl<N: Network, Private: Visibility<N>>> Value<N, Private> {
//     // /// Returns the recursive depth of this value.
//     // /// Note: Once `generic_const_exprs` is stabilized, this can be replaced with `const DEPTH: u8`.
//     // fn depth(&self, counter: usize) -> usize {
//     //     match self {
//     //         Self::Literal(..) => 1,
//     //         Self::Composite(composite) => {
//     //             // Determine the maximum depth of the composite.
//     //             let max_depth = composite.iter().map(|(_, value)| value.depth(counter)).fold(0, |a, b| a.max(b));
//     //             // Add `1` to the depth of the member with the largest depth.
//     //             max_depth.saturating_add(1)
//     //         }
//     //     }
//     // }
// }
