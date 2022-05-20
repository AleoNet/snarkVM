// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

mod hash;
mod hash_uncompressed;

use crate::Blake2Xs;
use snarkvm_console_types::prelude::*;
use snarkvm_utilities::BigInteger;

pub const SINSEMILLA_WINDOW_SIZE: usize = 14;
pub const SINSEMILLA_TABLE_SIZE: u32 = 16384; // 2^SINSEMILLA_WINDOW_SIZE

/// Sinsemilla256 is a collision-resistant hash function that takes up to a 256-bit input.
pub type Sinsemilla256<E> = Sinsemilla<E, 19>;
/// Sinsemilla512 is a collision-resistant hash function that takes up to a 512-bit input.
pub type Sinsemilla512<E> = Sinsemilla<E, 37>;
/// Sinsemilla768 is a collision-resistant hash function that takes up to a 768-bit input.
pub type Sinsemilla768<E> = Sinsemilla<E, 55>;
/// Sinsemilla1024 is a collision-resistant hash function that takes up to a 1024-bit input.
pub type Sinsemilla1024<E> = Sinsemilla<E, 74>;

/// Sinsemilla is a collision-resistant hash function that takes a fixed-length input.
/// The Sinsemilla hash function does *not* behave like a random oracle, see Poseidon for one.
pub struct Sinsemilla<E: Environment, const NUM_WINDOWS: u8> {
    q: Group<E>,
    p_lookups: Vec<Group<E>>,
}

impl<E: Environment, const NUM_WINDOWS: u8> Sinsemilla<E, NUM_WINDOWS> {
    /// Initializes a new instance of Sinsemilla with the given setup message.
    pub fn setup(message: &str) -> Self {
        // Calculate the maximum window size.
        let mut maximum_window_size = 0;
        let mut range = E::BigInteger::from(2_u64);
        while range < E::Scalar::modulus_minus_one_div_two() {
            // range < (p-1)/2
            range.muln(1);
            maximum_window_size += 1;
        }
        assert!(
            SINSEMILLA_WINDOW_SIZE <= maximum_window_size,
            "The maximum Sinsemilla window size is {maximum_window_size}"
        );

        // Compute Q
        let (generator, _, _) = Blake2Xs::hash_to_curve(message);
        let q = Group::<E>::new(generator);

        // Compute P[0..2^WINDOW_SIZE-1]
        let table_size = SINSEMILLA_TABLE_SIZE;
        let mut p_lookups = Vec::with_capacity(table_size as usize);
        for i in 0..table_size {
            let (generator, _, _) = Blake2Xs::hash_to_curve(&format!("{:?}", i.to_le_bytes()));
            let p = Group::<E>::new(generator);
            p_lookups.push(p);
        }

        Self { q, p_lookups }
    }

    pub fn q(&self) -> Group<E> {
        self.q
    }

    pub fn p_lookups(&self) -> &Vec<Group<E>> {
        &self.p_lookups
    }
}
