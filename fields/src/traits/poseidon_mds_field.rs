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

use crate::{FftParameters, PrimeField};

/// The interface for MDS parameters
pub trait PoseidonMDSParameters: 'static + Send + Sync + Sized + FftParameters {
    /// The 3x3 MDS matrix
    const POSEIDON_MDS: [[Self::BigInteger; 3]; 3];
    /// The alpha
    const POSEIDON_ALPHA: u64;
    /// The number of full rounds
    const POSEIDON_FULL_ROUNDS: u32;
    /// The number of partial rounds
    const POSEIDON_PARTIAL_ROUNDS: u32;
}

/// The interface for a prime field with Poseidon MDS matrix.
pub trait PoseidonMDSField: PrimeField {
    /// Returns the Poseidon parameters
    fn poseidon_mds_matrix() -> Vec<Vec<Self>>;

    /// Returns the Poseidon alpha value
    fn poseidon_alpha() -> u64;

    /// Returns the Poseidon number of full rounds
    fn poseidon_number_full_rounds() -> u32;

    /// Returns the Poseidon number of partial rounds
    fn poseidon_number_partial_rounds() -> u32;
}
