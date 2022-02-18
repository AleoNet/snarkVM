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

use anyhow::Result;
use snarkvm_curves::traits::PairingEngine;
use snarkvm_utilities::{CanonicalDeserialize, ConstantSerializedSize};

use std::{
    fs::{File, OpenOptions},
    io::{BufRead, BufReader, Cursor, Seek, SeekFrom},
    marker::PhantomData,
    path::PathBuf,
};

lazy_static::lazy_static! {
    static ref DEFAULT_PATH: PathBuf = PathBuf::from("~/.aleo/powers_of_g");
}
// TODO: add buckets here

/// An abstraction over a vector of powers of G, meant to reduce
/// memory burden when handling universal setup parameters.
pub struct PowersOfG<E: PairingEngine> {
    /// A handle to the file on disk containing the powers of G.
    file: File,
    /// The degree up to which we currently have powers.
    degree: usize,
    _phantom_data: PhantomData<E>,
}

impl<E: PairingEngine> Default for PowersOfG<E> {
    fn default() -> Self {
        Self::new(DEFAULT_PATH.clone()).unwrap()
    }
}

impl<E: PairingEngine> PowersOfG<E> {
    /// Returns a new instance of PowersOfG, which will store its
    /// powers in a file at `file_path`.
    pub fn new(file_path: PathBuf) -> Result<Self> {
        // Open the given file, creating it if it doesn't yet exist.
        let file = OpenOptions::new().read(true).create(true).open(file_path)?;

        // TODO: Check the degree we're on.

        Ok(Self { file, degree: 0, _phantom_data: PhantomData })
    }

    /// Return the degree of the current powers of G.
    pub fn len(&self) -> usize {
        self.degree
    }

    /// Returns an element at `index`.
    /// NOTE: `std::ops::Index` was not used here as the trait requires
    /// that we return a reference. We can not return a reference to
    /// something that does not exist when this function is called.
    pub fn index(&self, index: usize) -> E::G1Affine {
        let mut reader = BufReader::new(&self.file);
        // Move our offset to the start of the desired element.
        reader.seek(SeekFrom::Start(index.checked_mul(E::G1Affine::SERIALIZED_SIZE + 1).unwrap() as u64));

        // Now read it out, deserialize it, and return it.
        let mut buf = String::new();
        reader.read_line(&mut buf).unwrap();
        E::G1Affine::deserialize(&mut Cursor::new(buf)).unwrap()
    }
}
