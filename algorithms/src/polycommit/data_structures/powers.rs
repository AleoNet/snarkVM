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

use crate::polycommit::PCError;
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
    degree: u64,
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
    pub fn len(&self) -> u64 {
        self.degree
    }

    /// Returns an element at `index`.
    /// NOTE: `std::ops::Index` was not used here as the trait requires
    /// that we return a reference. We can not return a reference to
    /// something that does not exist when this function is called.
    pub fn index(&self, index: u64) -> Result<E::G1Affine> {
        let index_start = self.get_starting_index(index)?;

        // Move our offset to the start of the desired element.
        let mut reader = BufReader::new(&self.file);
        reader.seek(SeekFrom::Start(index_start));

        // Now read it out, deserialize it, and return it.
        let mut buf = String::new();
        reader.read_line(&mut buf)?;
        Ok(E::G1Affine::deserialize(&mut Cursor::new(buf))?)
    }

    /// Slices the underlying file to return a vector of affine elements
    /// between `lower` and `upper`.
    pub fn slice(&self, lower: u64, upper: u64) -> Result<Vec<E::G1Affine>> {
        if upper.checked_mul((E::G1Affine::SERIALIZED_SIZE + 1) as u64).ok_or(PCError::IndexOverflowed)?
            > self.file.metadata()?.len()
        {
            let degree = upper.next_power_of_two();
            self.download_up_to(degree)?;
        }

        let index_start = self.get_starting_index(lower)?;

        // Move our offset to the start of the desired element.
        let mut reader = BufReader::new(&self.file);
        reader.seek(SeekFrom::Start(index_start));

        // Now iterate until we fill a vector with all desired elements.
        let mut powers = Vec::with_capacity((upper - lower) as usize);
        for _ in lower..upper {
            let mut buf = String::new();
            reader.read_line(&mut buf)?;
            powers.push(E::G1Affine::deserialize(&mut Cursor::new(buf))?);
        }

        Ok(powers)
    }

    /// This function returns the starting byte of the file in which we're indexing
    /// our powers of G.
    fn get_starting_index(&self, index: u64) -> Result<u64> {
        let index_start =
            index.checked_mul((E::G1Affine::SERIALIZED_SIZE + 1) as u64).ok_or(PCError::IndexOverflowed)?;
        if index_start > self.file.metadata()?.len() {
            let degree = index.next_power_of_two();
            self.download_up_to(degree)?;
        }

        Ok(index_start)
    }

    /// Download the transcript up to `degree`.
    fn download_up_to(&self, degree: u64) -> Result<()> {
        unimplemented!()
    }
}
