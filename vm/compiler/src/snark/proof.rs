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

use super::*;

pub struct Proof<N: Network> {
    /// The proof.
    proof: marlin::Proof<Bls12_377>,
    /// PhantomData
    _phantom: PhantomData<N>,
}

impl<N: Network> Proof<N> {
    /// Initializes a new proof.
    pub(super) const fn new(proof: marlin::Proof<Bls12_377>) -> Self {
        Self { proof, _phantom: PhantomData }
    }
}

impl<N: Network> Deref for Proof<N> {
    type Target = marlin::Proof<Bls12_377>;

    fn deref(&self) -> &Self::Target {
        &self.proof
    }
}
