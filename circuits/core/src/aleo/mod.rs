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
use snarkvm_algorithms::crypto_hash::hash_to_curve;
use snarkvm_circuits_environment::prelude::*;
use snarkvm_circuits_types::{Field, Group, Scalar};

pub struct Aleo<E: Environment> {
    /// The Poseidon hash function.
    poseidon: Poseidon<E>,
    /// The group bases for the Aleo signature and encryption schemes.
    bases: Vec<Group<E>>,
}

impl<E: Environment> Aleo<E> {
    /// Initializes a new instance of the signature scheme from a given input domain message.
    pub fn new(message: &str) -> Self {
        // Hash the given message to a point on the curve, to initialize the starting base.
        let (base, _, _) = hash_to_curve::<E::Affine>(message);

        // Initialize the vector of bases.
        let mut bases = Vec::with_capacity(E::ScalarField::size_in_bits());

        // Compute the bases up to the size of the scalar field (in bits).
        let mut base = base.into_projective();
        for _ in 0..E::ScalarField::size_in_bits() {
            bases.push(Group::constant(base.into_affine()));
            base.double_in_place();
        }

        Self { poseidon: Poseidon::new(), bases }
    }
}
