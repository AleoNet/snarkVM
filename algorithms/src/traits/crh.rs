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

use crate::errors::CRHError;
use snarkvm_utilities::{FromBytes, ToBits, ToBytes};

use std::{
    fmt::{Debug, Display},
    hash::Hash,
};

pub trait CRH: Clone + Debug + PartialEq + Eq + Send + Sync {
    type Output: Copy + Clone + Debug + Display + ToBytes + FromBytes + PartialEq + Eq + Hash + Default + Send + Sync;
    type Parameters: Clone + Debug + Eq;

    fn setup(message: &str) -> Self;

    fn hash(&self, input: &[bool]) -> Result<Self::Output, CRHError>;

    fn hash_bytes(&self, input: &[u8]) -> Result<Self::Output, CRHError> {
        self.hash(&input.to_bits_le())
    }

    fn parameters(&self) -> &Self::Parameters;
}
