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

mod hash;
mod hash_uncompressed;

use crate::Blake2Xs;
use snarkvm_console_types::prelude::*;
use snarkvm_utilities::BigInteger;

const SINSEMILLA_WINDOW_SIZE: usize = 10;

/// Sinsemilla256 is a collision-resistant hash function that takes up to a 256-bit input.
pub type Sinsemilla256<E> = Sinsemilla<E, 26>;
/// Sinsemilla512 is a collision-resistant hash function that takes up to a 512-bit input.
pub type Sinsemilla512<E> = Sinsemilla<E, 52>;
/// Sinsemilla768 is a collision-resistant hash function that takes up to a 768-bit input.
pub type Sinsemilla768<E> = Sinsemilla<E, 77>;
/// Sinsemilla1024 is a collision-resistant hash function that takes up to a 1024-bit input.
pub type Sinsemilla1024<E> = Sinsemilla<E, 103>;

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
        let table_size = 2usize.pow(SINSEMILLA_WINDOW_SIZE as u32);
        let mut p_lookups = Vec::with_capacity(table_size);
        for i in 0..table_size {
            let (generator, _, _) = Blake2Xs::hash_to_curve(&format!("{:?}", (i as u32).to_le_bytes()));
            let p = Group::<E>::new(generator);
            p_lookups.push(p);
        }

        Self { q, p_lookups }
    }
}
