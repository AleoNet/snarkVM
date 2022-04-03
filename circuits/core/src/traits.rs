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

/// A trait for a hash function.
pub trait Hash {
    type Input;
    type Output;

    /// Returns the hash of the given input.
    fn hash(&self, input: &[Self::Input]) -> Self::Output;
}

/// A trait for a hash function of an uncompressed variant.
pub trait HashUncompressed {
    type Input;
    type Output;

    /// Returns the hash of the given input.
    fn hash_uncompressed(&self, input: &[Self::Input]) -> Self::Output;
}
