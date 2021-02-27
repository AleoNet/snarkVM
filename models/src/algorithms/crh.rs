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

use snarkvm_algorithms::errors::CRHError;
use snarkvm_utilities::bytes::{FromBytes, ToBytes};

use rand::Rng;
use std::{
    fmt::{Debug, Display},
    hash::Hash,
};

pub trait CRHParameters: Clone + Debug + ToBytes + FromBytes + Eq {
    fn setup<R: Rng>(r: &mut R) -> Self;
}

pub trait CRH: Clone + From<<Self as CRH>::Parameters> {
    type Output: Clone + Debug + Display + ToBytes + FromBytes + Eq + Hash + Default;
    type Parameters: CRHParameters;

    const INPUT_SIZE_BITS: usize;

    fn setup<R: Rng>(r: &mut R) -> Self;

    fn hash(&self, input: &[u8]) -> Result<Self::Output, CRHError>;

    fn parameters(&self) -> &Self::Parameters;
}
