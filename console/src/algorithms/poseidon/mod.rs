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

mod helpers;

mod hash;
mod hash_many;
mod hash_to_scalar;
mod prf;

use crate::algorithms::{poseidon::helpers::*, Hash, HashMany, HashToScalar, PRF};
use snarkvm_fields::{PoseidonParameters, PrimeField};

use anyhow::{bail, Result};
use std::sync::Arc;

const CAPACITY: usize = 1;

/// Poseidon2 is a cryptographic hash function of input rate 2.
pub type Poseidon2<F> = Poseidon<F, 2>;
/// Poseidon4 is a cryptographic hash function of input rate 4.
pub type Poseidon4<F> = Poseidon<F, 4>;
/// Poseidon8 is a cryptographic hash function of input rate 8.
pub type Poseidon8<F> = Poseidon<F, 8>;

pub struct Poseidon<F: PrimeField, const RATE: usize> {
    /// The Poseidon parameters for hashing.
    parameters: Arc<PoseidonParameters<F, RATE, CAPACITY>>,
}

impl<F: PrimeField, const RATE: usize> Poseidon<F, RATE> {
    /// Initializes a new instance of Poseidon.
    pub fn setup() -> Self {
        Self { parameters: Arc::new(F::default_poseidon_parameters::<RATE>().unwrap()) }
    }
}
