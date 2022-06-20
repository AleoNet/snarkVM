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

mod commit;
mod commit_uncompressed;
mod hash;
mod hash_uncompressed;

use crate::Blake2Xs;
use snarkvm_console_types::prelude::*;

use std::{borrow::Cow, sync::Arc};

/// Pedersen64 is an *additively-homomorphic* collision-resistant hash function that takes up to a 64-bit input.
pub type Pedersen64<E> = Pedersen<E, 64>;
/// Pedersen128 is an *additively-homomorphic* collision-resistant hash function that takes up to a 128-bit input.
pub type Pedersen128<E> = Pedersen<E, 128>;

/// Pedersen is a collision-resistant hash function that takes a variable-length input.
/// The Pedersen hash function does *not* behave like a random oracle, see Poseidon for one.
#[derive(Clone)]
pub struct Pedersen<E: Environment, const NUM_BITS: u8> {
    /// The base window for the Pedersen hash.
    base_window: Arc<Vec<Group<E>>>,
    /// The random base window for the Pedersen commitment.
    random_base_window: Arc<Vec<Group<E>>>,
}

impl<E: Environment, const NUM_BITS: u8> Pedersen<E, NUM_BITS> {
    /// Initializes a new instance of Pedersen with the given setup message.
    pub fn setup(message: &str) -> Self {
        // Construct an indexed message to attempt to sample a base.
        let (generator, _, _) = Blake2Xs::hash_to_curve::<E::Affine>(&format!("Aleo.Pedersen.Base.{message}"));
        // Construct the window with the base.
        let mut base_window = vec![Group::<E>::zero(); NUM_BITS as usize];
        {
            let mut base_power = Group::<E>::new(generator);
            for base in base_window.iter_mut().take(NUM_BITS as usize) {
                *base = base_power;
                base_power = base_power.double();
            }
            assert_eq!(base_window.len(), NUM_BITS as usize);
        }

        // Compute the random base.
        let (generator, _, _) = Blake2Xs::hash_to_curve::<E::Affine>(&format!("Aleo.Pedersen.RandomBase.{message}"));
        // Construct the window with the random base.
        let mut random_base = Vec::with_capacity(Scalar::<E>::size_in_bits());
        {
            let mut base = Group::<E>::new(generator);
            for _ in 0..Scalar::<E>::size_in_bits() {
                random_base.push(base);
                base = base.double();
            }
            assert_eq!(random_base.len(), Scalar::<E>::size_in_bits());
        }

        Self { base_window: Arc::new(base_window.to_vec()), random_base_window: Arc::new(random_base) }
    }

    /// Returns the base window.
    pub fn base_window(&self) -> &Arc<Vec<Group<E>>> {
        &self.base_window
    }

    /// Returns the random base window.
    pub fn random_base_window(&self) -> &Arc<Vec<Group<E>>> {
        &self.random_base_window
    }
}
