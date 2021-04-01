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

/// A `enum` specifying the possible failure modes of `FiatShamir`.
#[derive(Debug)]
pub enum FiatShamirError {
    /// There was a synthesis error.
    R1CSError(snarkvm_r1cs::SynthesisError),
    /// The RNG has not been initialized.
    UninitializedRNG,
}

impl From<snarkvm_r1cs::SynthesisError> for FiatShamirError {
    fn from(err: snarkvm_r1cs::SynthesisError) -> Self {
        FiatShamirError::R1CSError(err)
    }
}
