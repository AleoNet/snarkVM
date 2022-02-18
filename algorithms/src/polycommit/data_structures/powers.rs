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

use snarkvm_curves::traits::PairingEngine;

use std::{marker::PhantomData, ops::Index, path::PathBuf};

lazy_static::lazy_static! {
    static ref DEFAULT_PATH: PathBuf = PathBuf::from("~/.aleo/powers_of_g");
}
// TODO: add buckets here

/// An abstraction over a vector of powers of G, meant to reduce
/// memory burden when handling universal setup parameters.
pub struct PowersOfG<E: PairingEngine> {
    /// The file on disk where the powers are stored.
    file_path: PathBuf,
    _phantom_data: PhantomData<E>,
}

impl<E: PairingEngine> Default for PowersOfG<E> {
    fn default() -> Self {
        Self::new(DEFAULT_PATH.clone())
    }
}

// Make our abstraction indexable, just like a vector would be, to make
// it easier to work with.
impl<E: PairingEngine> Index<usize> for PowersOfG<E> {
    type Output = E::G1Affine;

    fn index(&self, index: usize) -> &Self::Output {
        unimplemented!()
    }
}

impl<E: PairingEngine> PowersOfG<E> {
    /// Returns a new instance of PowersOfG, which will store its
    /// powers in a file at `file_path`.
    pub fn new(file_path: PathBuf) -> Self {
        Self { file_path, _phantom_data: PhantomData }
    }
}
