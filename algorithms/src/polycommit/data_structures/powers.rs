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
use rand::Rng;
use snarkvm_curves::traits::PairingEngine;
use snarkvm_utilities::{
    CanonicalDeserialize,
    CanonicalSerialize,
    ConstantSerializedSize,
    FromBytes,
    Read,
    SerializationError,
    ToBytes,
    Write,
};

use parking_lot::RwLock;
use std::{
    fs::{File, OpenOptions},
    io::{BufReader, Seek, SeekFrom},
    marker::PhantomData,
    path::PathBuf,
    sync::Arc,
};

lazy_static::lazy_static! {
    static ref DEFAULT_PATH: PathBuf = PathBuf::from("~/.aleo/powers_of_g");
}
// TODO: add buckets here

/// An abstraction over a vector of powers of G, meant to reduce
/// memory burden when handling universal setup parameters.
#[derive(Derivative)]
#[derivative(Debug(bound = ""))]
pub struct PowersOfG<E: PairingEngine> {
    /// Filepath of the powers we're using.
    file_path: String,
    /// A handle to the file on disk containing the powers of G.
    /// The handle is guarded to avoid read/write conflicts with potential
    /// clones.
    #[derivative(Debug = "ignore")]
    file: Arc<RwLock<File>>,
    /// The degree up to which we currently have powers.
    degree: u64,
    _phantom_data: PhantomData<E>,
}

impl<E: PairingEngine> Default for PowersOfG<E> {
    fn default() -> Self {
        // This basically should never fail, hence the expect call.
        Self::new(DEFAULT_PATH.clone()).expect("could not create default powers of G")
    }
}

impl<E: PairingEngine> Clone for PowersOfG<E> {
    fn clone(&self) -> Self {
        Self::new(PathBuf::from(self.file_path.clone())).expect("could not clone powers of g")
    }
}

impl<E: PairingEngine> CanonicalSerialize for PowersOfG<E> {
    fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), SerializationError> {
        CanonicalSerialize::serialize(&self.file_path, writer)
    }

    fn serialized_size(&self) -> usize {
        self.file_path.len() + 8
    }
}

impl<E: PairingEngine> CanonicalDeserialize for PowersOfG<E> {
    fn deserialize<R: Read>(reader: &mut R) -> Result<Self, SerializationError> {
        let file_path = String::deserialize(reader)?;
        Self::new(PathBuf::from(file_path)).map_err(|_| SerializationError::InvalidData)
    }
}

// NOTE: this drops the powers into a tmp file.
// I assume this is only used for testing but this needs to be verified.
impl<E: PairingEngine> From<Vec<E::G1Affine>> for PowersOfG<E> {
    fn from(value: Vec<E::G1Affine>) -> Self {
        let mut dir = std::env::temp_dir();
        dir.push(format!("powers_of_g_{}", rand::thread_rng().gen::<u32>()));
        let mut file = OpenOptions::new()
            .write(true)
            .truncate(true)
            .create(true)
            .open(dir.clone())
            .expect("should be able to create tmp powers of g");

        (value.len() as u32).write_le(&mut file).unwrap();
        for power in value {
            power.serialize(&mut file).unwrap();
        }

        drop(file);
        Self::new(dir).unwrap()
    }
}

impl<E: PairingEngine> PowersOfG<E> {
    /// Returns a new instance of PowersOfG, which will store its
    /// powers in a file at `file_path`.
    pub fn new(file_path: PathBuf) -> Result<Self> {
        // Open the given file, creating it if it doesn't yet exist.
        let mut file = OpenOptions::new().read(true).write(true).create(true).open(file_path.clone())?;
        let degree = if file.metadata()?.len() > 0 { u32::read_le(&mut file).unwrap() as u64 } else { 0 };

        Ok(Self {
            file_path: String::from(file_path.to_str().expect("could not get filepath for powers of g")),
            file: Arc::new(RwLock::new(file)),
            degree,
            _phantom_data: PhantomData,
        })
    }

    /// Return the number of current powers of G.
    pub fn len(&self) -> usize {
        self.degree as usize
    }

    /// Returns whether or not the current powers of G are empty.
    pub fn is_empty(&self) -> bool {
        self.degree == 0
    }

    /// Returns an element at `index`.
    /// NOTE: `std::ops::Index` was not used here as the trait requires
    /// that we return a reference. We can not return a reference to
    /// something that does not exist when this function is called.
    pub fn index(&self, index: usize) -> E::G1Affine {
        let index_start = self.get_starting_index(index);

        // Move our offset to the start of the desired element.
        let file = self.file.read();
        let mut reader = BufReader::new(&*file);
        reader.seek(SeekFrom::Start(index_start as u64)).expect("could not seek to element starting index");

        // Now read it out, deserialize it, and return it.
        E::G1Affine::deserialize(&mut reader).expect("powers of g corrupted")
    }

    /// Slices the underlying file to return a vector of affine elements
    /// between `lower` and `upper`.
    pub fn slice(&self, lower: usize, upper: usize) -> Vec<E::G1Affine> {
        self.ensure_powers_exist(upper);
        let index_start = self.get_starting_index(lower);

        // Move our offset to the start of the desired element.
        let file = self.file.read();
        let mut reader = BufReader::new(&*file);
        reader.seek(SeekFrom::Start(index_start as u64)).expect("could not seek to element starting index");

        // Now iterate until we fill a vector with all desired elements.
        let mut powers = Vec::with_capacity((upper - lower) as usize);
        for _ in lower..upper {
            let power = E::G1Affine::deserialize(&mut reader).expect("powers of g corrupted");
            powers.push(power);
        }

        powers
    }

    /// This function returns the starting byte of the file in which we're indexing
    /// our powers of G.
    fn get_starting_index(&self, index: usize) -> usize {
        let index_start = index
            .checked_mul(E::G1Affine::SERIALIZED_SIZE)
            .expect("attempted to index powers of G with an index greater than usize")
            + 4;
        self.ensure_powers_exist(index_start);

        index_start
    }

    fn ensure_powers_exist(&self, index: usize) {
        if index > self.file.read().metadata().expect("could not get powers of G metadata").len() as usize {
            let degree = index.next_power_of_two();
            self.download_up_to(degree).expect("could not download missing powers of G");
        }
    }

    /// Download the transcript up to `degree`.
    fn download_up_to(&self, _degree: usize) -> Result<()> {
        unimplemented!()
    }
}
