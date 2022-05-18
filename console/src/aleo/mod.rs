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

pub mod account;
pub use account::*;

pub mod testnet3;
pub use testnet3::*;

use snarkvm_algorithms::prelude::*;
use snarkvm_curves::{AffineCurve, TwistedEdwardsParameters};
use snarkvm_fields::traits::*;

use anyhow::Result;
use core::{fmt, hash};

pub trait Network: Copy + Clone + fmt::Debug + Eq + PartialEq + hash::Hash {
    type Affine: AffineCurve<BaseField = Self::Field, Coordinates = (Self::Field, Self::Field)>;
    type AffineParameters: TwistedEdwardsParameters<BaseField = Self::Field>;
    type Field: PrimeField + Copy;
    type Scalar: PrimeField + Copy;

    /// PRF for deriving the account private key from a seed.
    type AccountPRF: PRF<Input = Vec<Self::Scalar>, Seed = Self::Scalar, Output = Self::Scalar>;

    /// The maximum number of bytes allowed in a string.
    const NUM_STRING_BYTES: u32;

    /// A helper method to recover the y-coordinate given the x-coordinate for
    /// a twisted Edwards point, returning the affine curve point.
    fn affine_from_x_coordinate(x: Self::Field) -> Result<Self::Affine>;
}
