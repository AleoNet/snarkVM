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

mod block;
pub use block::*;

mod transaction;
pub use transaction::*;

mod transition;
pub use transition::*;

use std::borrow::Cow;

/// A wrapper enum able to contain and iterate over two `Cow` iterators of different types.
enum CowIter<'a, T: 'a + Clone, I1: Iterator<Item = &'a T>, I2: Iterator<Item = T>> {
    Borrowed(I1),
    Owned(I2),
    None,
}

impl<'a, T: 'a + Clone, I1: Iterator<Item = &'a T>, I2: Iterator<Item = T>> Iterator for CowIter<'a, T, I1, I2> {
    type Item = Cow<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Borrowed(iter) => Some(Cow::Borrowed(iter.next()?)),
            Self::Owned(iter) => Some(Cow::Owned(iter.next()?)),
            Self::None => None,
        }
    }
}

#[macro_export]
macro_rules! unwrap_cow {
    ($cow:expr) => {
        match $cow {
            Cow::Borrowed(inner) => (*inner).clone(),
            Cow::Owned(inner) => inner,
        }
    };
}
