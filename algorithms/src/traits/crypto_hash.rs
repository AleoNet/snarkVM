// Copyright (C) 2019-2021 Aleo Systems Inc.
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

use snarkvm_utilities::{
    bytes::{FromBytes, ToBytes},
    fmt::Debug,
};

pub trait CryptoHash {
    type Input: FromBytes + From<u64> + Clone;
    type Output: Copy + Clone + Debug + ToBytes + Eq + Default;
    type Parameters: Clone + Debug + Eq;

    /// Initializes a new instance of the cryptographic hash function.
    fn setup() -> Self;

    /// Evaluate the cryptographic hash function over a fixed-length vector as input.
    fn evaluate(&self, input: &[Self::Input]) -> Self::Output;

    /// Evaluate the cryptographic hash function over a non-fixed-length vector,
    /// in which the length also needs to be hashed.
    fn evaluate_with_len(&self, input: &[Self::Input]) -> Self::Output {
        let mut header = vec![<Self::Input as From<u64>>::from(input.len() as u64)];
        header.extend_from_slice(input);
        self.evaluate(&header)
    }

    fn parameters(&self) -> &Self::Parameters;
}
