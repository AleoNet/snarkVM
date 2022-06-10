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

use anyhow::Result;

/// A trait for a commitment scheme.
pub trait Commit {
    type Input;
    type Output;
    type Randomizer;

    /// Returns the commitment to the given input and randomizer.
    fn commit(&self, input: &[Self::Input], randomizer: &Self::Randomizer) -> Result<Self::Output>;
}

/// A trait for a commitment scheme.
pub trait CommitUncompressed {
    type Input;
    type Output;
    type Randomizer;

    /// Returns the commitment to the given input and randomizer.
    fn commit_uncompressed(&self, input: &[Self::Input], randomizer: &Self::Randomizer) -> Result<Self::Output>;
}

/// A trait for a hash function.
pub trait Hash {
    type Input;
    type Output;

    /// Returns the hash of the given input.
    fn hash(&self, input: &[Self::Input]) -> Result<Self::Output>;
}

/// A trait for a hash function that produces multiple outputs.
pub trait HashMany {
    type Input;
    type Output;

    /// Returns the hash of the given input.
    fn hash_many(&self, input: &[Self::Input], num_outputs: u16) -> Vec<Self::Output>;
}

/// A trait for a hash function that projects the value to an affine group element.
pub trait HashToGroup {
    type Input;
    type Output;

    /// Returns the hash of the given input.
    fn hash_to_group(&self, input: &[Self::Input]) -> Result<Self::Output>;
}

/// A trait for a hash function that projects the value to a scalar.
pub trait HashToScalar {
    type Input;
    type Output;

    /// Returns the hash of the given input.
    fn hash_to_scalar(&self, input: &[Self::Input]) -> Result<Self::Output>;
}

/// A trait for a hash function of an uncompressed variant.
pub trait HashUncompressed {
    type Input;
    type Output;

    /// Returns the hash of the given input.
    fn hash_uncompressed(&self, input: &[Self::Input]) -> Result<Self::Output>;
}

/// A trait for a pseudorandom function.
pub trait PRF {
    type Seed;
    type Input;
    type Output;

    /// Returns the output for the given seed and input.
    fn prf(&self, seed: &Self::Seed, input: &[Self::Input]) -> Result<Self::Output>;
}
