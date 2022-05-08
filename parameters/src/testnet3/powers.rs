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

use super::*;
use snarkvm_curves::traits::PairingEngine;
use snarkvm_utilities::{
    CanonicalDeserialize,
    CanonicalSerialize,
    FromBytes,
    Read,
    SerializationError,
    ToBytes,
    Write,
};

use anyhow::{bail, Result};
use itertools::Itertools;
use rand::Rng;
use std::{
    collections::BTreeMap,
    fs::{File, OpenOptions},
    io::{BufReader, Seek, SeekFrom},
    path::PathBuf,
};

lazy_static::lazy_static! {
    static ref DEFAULT_PATH: PathBuf = PathBuf::from(format!("{}/.aleo/powers_of_g", std::env::var("HOME").unwrap()));
    static ref UNIVERSAL_SRS_15: Vec<u8> = Degree15::load_bytes().expect("Failed to load universal SRS of degree 15");
    static ref POWERS_TIMES_GAMMA_G: &'static [u8] = include_bytes!("./gamma_powers");
}

// Amount of powers contained in `POWERS_TIMES_GAMMA_G`.
const NUM_POWERS_TIMES_GAMMA_G: usize = 84;
// Size of a serialized power of G.
const POWER_OF_G_SERIALIZED_SIZE: usize = 97;

const DEGREE_16: usize = 1 << 16;
const DEGREE_17: usize = 1 << 17;
const DEGREE_18: usize = 1 << 18;
const DEGREE_19: usize = 1 << 19;
const DEGREE_20: usize = 1 << 20;
const DEGREE_21: usize = 1 << 21;
const DEGREE_22: usize = 1 << 22;
const DEGREE_23: usize = 1 << 23;
const DEGREE_24: usize = 1 << 24;
const DEGREE_25: usize = 1 << 25;
const DEGREE_26: usize = 1 << 26;
const DEGREE_27: usize = 1 << 27;
const DEGREE_28: usize = 1 << 28;

/// An abstraction over a vector of powers of G, meant to reduce
/// memory burden when handling universal setup parameters.
#[derive(Debug)]
pub struct PowersOfG<E: PairingEngine> {
    /// Filepath of the powers we're using.
    file_path: String,
    /// A handle to the file on disk containing the powers of G.
    /// The handle is guarded to avoid read/write conflicts with potential
    /// clones.
    /// Contains group elements of the form `[G, \beta * G, \beta^2 * G, ..., \beta^{d} G]`.
    file: File,
    /// Group elements of the form `{ \beta^i \gamma G }`, where `i` ranges from 0 to `degree`.
    /// These are used for hiding.
    powers_of_beta_times_gamma_g: BTreeMap<usize, E::G1Affine>,
    /// The degree up to which we have powers.
    /// Mostly just used for ensuring we download in the proper order,
    /// length checks are actually done by checking file metadata.
    degree: usize,
}

// NOTE: this drops the powers into a tmp file.
// I assume this is only used for testing but this needs to be verified.
impl<E: PairingEngine> From<(Vec<E::G1Affine>, BTreeMap<usize, E::G1Affine>)> for PowersOfG<E> {
    fn from(value: (Vec<E::G1Affine>, BTreeMap<usize, E::G1Affine>)) -> Self {
        let mut dir = std::env::temp_dir();
        dir.push(format!("powers_of_g_{}", rand::thread_rng().gen::<u32>()));
        let mut file = OpenOptions::new()
            .write(true)
            .truncate(true)
            .create(true)
            .open(dir.clone())
            .expect("should be able to create tmp powers of g");

        for power in value.0 {
            power.write_le(&mut file).unwrap();
        }

        drop(file);
        let mut powers = Self::new(dir).unwrap();
        powers.powers_of_beta_times_gamma_g = value.1;
        powers
    }
}

impl<E: PairingEngine> PowersOfG<E> {
    /// Returns a new instance of `PowersOfG`, which will store its
    /// powers in a file at `file_path`.
    pub fn new(file_path: PathBuf) -> Result<Self> {
        // Open the given file, creating it if it doesn't yet exist.
        let mut file = OpenOptions::new().read(true).write(true).create(true).open(file_path.clone())?;

        // If the file is empty, let's write the base powers (up to degree 15) to it.
        if file.metadata()?.len() == 0 {
            file.write_all(&UNIVERSAL_SRS_15)?;
        }

        let degree = file.metadata()?.len() as usize / POWER_OF_G_SERIALIZED_SIZE;

        let mut powers = Self {
            file_path: String::from(file_path.to_str().expect("could not get filepath for powers of g")),
            file,
            powers_of_beta_times_gamma_g: BTreeMap::new(),
            degree,
        };

        powers.regenerate_powers_of_beta_times_gamma_g();
        Ok(powers)
    }

    /// Return the number of current powers of G.
    pub fn degree(&self) -> usize {
        self.degree
    }

    /// Returns the power of beta times G specified by `which_power`.
    // NOTE: `std::ops::Index` was not used here as the trait requires
    // that we return a reference. We can not return a reference to
    // something that does not exist when this function is called.
    pub fn power_of_beta_g(&mut self, which_power: usize) -> E::G1Affine {
        let index_start = self.get_starting_index(which_power);

        // Move our offset to the start of the desired element.
        let mut reader = BufReader::new(&self.file);
        reader.seek(SeekFrom::Start(index_start as u64)).expect("could not seek to element starting index");

        // Now read it out, deserialize it, and return it.
        FromBytes::read_le(&mut reader).expect("powers of g corrupted")
    }

    /// Slices the underlying file to return a vector of affine elements
    /// between `lower` and `upper`.
    pub fn powers_of_beta_g(&mut self, lower: usize, upper: usize) -> Vec<E::G1Affine> {
        // Ensure index exists for upper power.
        let _ = self.get_starting_index(upper);
        let index_start = self.get_starting_index(lower);

        // Move our offset to the start of the desired element.
        let mut reader = BufReader::new(&self.file);
        reader.seek(SeekFrom::Start(index_start as u64)).expect("could not seek to element starting index");

        // Now iterate until we fill a vector with all desired elements.
        let mut powers = Vec::with_capacity((upper - lower) as usize);
        for _ in lower..upper {
            let power: E::G1Affine = FromBytes::read_le(&mut reader).expect("powers of g corrupted");
            powers.push(power);
        }

        powers
    }

    /// This function returns the starting byte of the file in which we're indexing
    /// our powers of G.
    fn get_starting_index(&mut self, index: usize) -> usize {
        let index_start = index
            .checked_mul(POWER_OF_G_SERIALIZED_SIZE)
            .expect("attempted to index powers of G with an index greater than usize");

        // Ensure the powers exist.
        if index_start > self.file.metadata().expect("could not get powers of G metadata").len() as usize {
            let degree = index_start.next_power_of_two();
            self.download_up_to(degree).expect("could not download missing powers of G");
        }

        index_start
    }

    /// This method downloads the universal SRS powers up to the `next_power_of_two(target_degree)`,
    /// and updates `Self` in place with the new powers.
    pub fn download_up_to(&mut self, target_degree: usize) -> Result<()> {
        // Determine the degrees to download.
        let mut degrees_to_download = vec![];
        let mut current = self.degree;
        while current < target_degree {
            degrees_to_download.push(current * 2);
            current *= 2;
        }

        // If the `target_degree` exceeds the current `degree`, proceed to download the new powers.
        if !degrees_to_download.is_empty() {
            for degree in &degrees_to_download {
                // Download the universal SRS powers.
                let bytes = match *degree {
                    DEGREE_16 => Degree16::load_bytes()?,
                    DEGREE_17 => Degree17::load_bytes()?,
                    DEGREE_18 => Degree18::load_bytes()?,
                    DEGREE_19 => Degree19::load_bytes()?,
                    DEGREE_20 => Degree20::load_bytes()?,
                    DEGREE_21 => Degree21::load_bytes()?,
                    DEGREE_22 => Degree22::load_bytes()?,
                    DEGREE_23 => Degree23::load_bytes()?,
                    DEGREE_24 => Degree24::load_bytes()?,
                    DEGREE_25 => Degree25::load_bytes()?,
                    DEGREE_26 => Degree26::load_bytes()?,
                    DEGREE_27 => Degree27::load_bytes()?,
                    DEGREE_28 => Degree28::load_bytes()?,
                    _ => bail!("Invalid degree '{degree}' selected"),
                };

                // Write the powers to the file.
                self.file.seek(SeekFrom::End(0))?;
                self.file.write_all(&bytes)?;

                // Update the `degree`.
                self.degree = *degree;
            }

            self.regenerate_powers_of_beta_times_gamma_g();
        }

        Ok(())
    }

    fn regenerate_powers_of_beta_times_gamma_g(&mut self) {
        let mut alpha_powers_g1 = vec![];
        let mut reader = BufReader::new(*POWERS_TIMES_GAMMA_G);
        for _ in 0..NUM_POWERS_TIMES_GAMMA_G {
            let power: E::G1Affine =
                FromBytes::read_le(&mut reader).expect("hardcoded powers times gamma g should be well-formed");
            alpha_powers_g1.push(power);
        }

        let mut alpha_tau_powers_g1 = BTreeMap::new();
        for (i, power) in alpha_powers_g1.iter().enumerate().take(3) {
            alpha_tau_powers_g1.insert(i, *power);
        }
        alpha_powers_g1[3..].iter().chunks(3).into_iter().enumerate().for_each(|(i, c)| {
            // Avoid underflows and just stop populating the map if we're going to.
            if self.degree() - 1 > (1 << i) {
                let c = c.into_iter().collect::<Vec<_>>();
                alpha_tau_powers_g1.insert(self.degree() - 1 - (1 << i) + 2, *c[0]);
                alpha_tau_powers_g1.insert(self.degree() - 1 - (1 << i) + 3, *c[1]);
                alpha_tau_powers_g1.insert(self.degree() - 1 - (1 << i) + 4, *c[2]);
            }
        });

        self.powers_of_beta_times_gamma_g = alpha_tau_powers_g1;
    }

    pub fn get_powers_times_gamma_g(&self) -> &BTreeMap<usize, E::G1Affine> {
        &self.powers_of_beta_times_gamma_g
    }
}

impl<E: PairingEngine> ToBytes for PowersOfG<E> {
    fn write_le<W: Write>(&self, mut writer: W) -> std::io::Result<()> {
        bincode::serialize_into(&mut writer, &self.file_path).unwrap();

        // Serialize `powers_of_beta_times_gamma_g`.
        (self.powers_of_beta_times_gamma_g.len() as u32).write_le(&mut writer)?;
        for (key, power_of_gamma_g) in &self.powers_of_beta_times_gamma_g {
            (*key as u32).write_le(&mut writer)?;
            power_of_gamma_g.write_le(&mut writer)?;
        }

        Ok(())
    }
}

impl<E: PairingEngine> FromBytes for PowersOfG<E> {
    fn read_le<R: Read>(mut reader: R) -> std::io::Result<Self> {
        let file_path: String = bincode::deserialize_from(&mut reader).unwrap();

        // Deserialize `powers_of_beta_times_gamma_g`.
        let mut powers_of_beta_times_gamma_g = BTreeMap::new();
        let powers_of_gamma_g_num_elements: u32 = FromBytes::read_le(&mut reader)?;
        for _ in 0..powers_of_gamma_g_num_elements {
            let key: u32 = FromBytes::read_le(&mut reader)?;
            let power_of_gamma_g: E::G1Affine = FromBytes::read_le(&mut reader)?;

            powers_of_beta_times_gamma_g.insert(key as usize, power_of_gamma_g);
        }

        let mut powers = PowersOfG::new(PathBuf::from(file_path)).unwrap();
        powers.powers_of_beta_times_gamma_g = powers_of_beta_times_gamma_g;
        Ok(powers)
    }
}

impl<E: PairingEngine> CanonicalSerialize for PowersOfG<E> {
    fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), SerializationError> {
        self.write_le(&mut *writer)?;
        Ok(())
    }

    fn serialized_size(&self) -> usize {
        todo!()
    }
}

impl<E: PairingEngine> CanonicalDeserialize for PowersOfG<E> {
    fn deserialize<R: Read>(reader: &mut R) -> Result<Self, SerializationError> {
        Ok(FromBytes::read_le(&mut *reader)?)
    }
}
