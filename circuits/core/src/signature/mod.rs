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

pub mod sign;

use crate::Poseidon;
use snarkvm_circuits_environment::prelude::*;
use snarkvm_circuits_types::{Field, Scalar};

pub struct Aleo<E: Environment> {
    /// The Poseidon hash function.
    poseidon: Poseidon<E>,
    /// The group bases for Aleo signatures.
}

impl<E: Environment> Aleo<E> {
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        let (base, _, _) = hash_to_curve::<TEAffine<TE>>(message);

        let mut g = base.into_projective();
        let mut g_bases = Vec::with_capacity(TE::ScalarField::size_in_bits());
        for _ in 0..TE::ScalarField::size_in_bits() {
            g_bases.push(g);
            g.double_in_place();
        }
        g_bases

        Self { poseidon: Poseidon::new() }
    }
}
