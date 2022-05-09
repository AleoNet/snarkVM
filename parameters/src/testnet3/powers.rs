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
    Compress,
    FromBytes,
    Read,
    SerializationError,
    ToBytes,
    Valid,
    Validate,
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
    static ref UNIVERSAL_SRS_15: Vec<u8> = Degree15::load_bytes().expect("Failed to load universal SRS of degree 15");
    static ref UNIVERSAL_SRS_GAMMA: Vec<u8> = Gamma::load_bytes().expect("Failed to load universal SRS gamma powers");
}

// Amount of powers contained in `UNIVERSAL_SRS_GAMMA`.
const NUM_UNIVERSAL_SRS_GAMMA: usize = 84;
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

        powers.regenerate_powers_of_beta_times_gamma_g()?;
        Ok(powers)
    }

    /// Return the number of current powers of G.
    pub fn degree(&self) -> usize {
        self.degree
    }

    /// Returns the power of beta times G specified by `target_power`.
    // NOTE: `std::ops::Index` was not used here as the trait requires
    // that we return a reference. We can not return a reference to
    // something that does not exist when this function is called.
    pub fn power_of_beta_g(&mut self, target_power: usize) -> E::G1Affine {
        let index_start = self.get_starting_byte_index(target_power).expect("Failed to load starting byte index");

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
        let _ = self.get_starting_byte_index(upper).expect("Failed to load upper power index");
        let index_start = self.get_starting_byte_index(lower).expect("Failed to load lower power index");

        // Move our offset to the start of the desired element.
        let mut reader = BufReader::new(&self.file);
        reader.seek(SeekFrom::Start(index_start as u64)).expect("could not seek to element starting index");

        // Now iterate until we fill a vector with all desired elements.
        let mut powers = Vec::with_capacity((upper - lower) as usize);
        for _ in lower..upper {
            powers.push(E::G1Affine::read_le(&mut reader).expect("powers of g corrupted"));
        }
        powers
    }

    /// Returns the index in the `file` for the starting byte of the `target_power` being requested.
    fn get_starting_byte_index(&mut self, target_power: usize) -> Result<usize> {
        let starting_byte_index = match target_power.checked_mul(POWER_OF_G_SERIALIZED_SIZE) {
            Some(index) => index,
            None => bail!("Attempted to load {target_power}th power of G, exceeding the bounds"),
        };

        // Ensure the powers exist, and download the missing powers if necessary.
        if starting_byte_index > self.file.metadata()?.len() as usize {
            self.download_up_to(target_power.next_power_of_two())?;
        }

        Ok(starting_byte_index)
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

            self.regenerate_powers_of_beta_times_gamma_g()?;
        }

        Ok(())
    }

    fn regenerate_powers_of_beta_times_gamma_g(&mut self) -> Result<()> {
        let mut alpha_powers_g1 = vec![];
        let mut reader = BufReader::new(UNIVERSAL_SRS_GAMMA.as_slice());
        for _ in 0..NUM_UNIVERSAL_SRS_GAMMA {
            alpha_powers_g1.push(E::G1Affine::read_le(&mut reader)?);
        }

        let mut alpha_tau_powers_g1 = BTreeMap::new();
        for (i, power) in alpha_powers_g1.iter().enumerate().take(3) {
            alpha_tau_powers_g1.insert(i, *power);
        }
        alpha_powers_g1[3..].iter().chunks(3).into_iter().enumerate().for_each(|(i, powers)| {
            // Avoid underflows and just stop populating the map if we're going to.
            if self.degree() - 1 > (1 << i) {
                let powers = powers.into_iter().collect::<Vec<_>>();
                alpha_tau_powers_g1.insert(self.degree() - 1 - (1 << i) + 2, *powers[0]);
                alpha_tau_powers_g1.insert(self.degree() - 1 - (1 << i) + 3, *powers[1]);
                alpha_tau_powers_g1.insert(self.degree() - 1 - (1 << i) + 4, *powers[2]);
            }
        });

        self.powers_of_beta_times_gamma_g = alpha_tau_powers_g1;

        Ok(())
    }

    pub fn get_powers_times_gamma_g(&self) -> &BTreeMap<usize, E::G1Affine> {
        &self.powers_of_beta_times_gamma_g
    }
}

impl<E: PairingEngine> ToBytes for PowersOfG<E> {
    fn write_le<W: Write>(&self, writer: W) -> std::io::Result<()> {
        self.serialize_with_mode(writer, Compress::Yes).map_err(|e| e.into())
    }
}

impl<E: PairingEngine> FromBytes for PowersOfG<E> {
    fn read_le<R: Read>(reader: R) -> std::io::Result<Self> {
        Self::deserialize_with_mode(reader, Compress::Yes, Validate::Yes).map_err(|e| e.into())
    }
}

impl<E: PairingEngine> CanonicalSerialize for PowersOfG<E> {
    fn serialize_with_mode<W: Write>(&self, mut writer: W, mode: Compress) -> Result<(), SerializationError> {
        bincode::serialize_into(&mut writer, &self.file_path).unwrap();

        // Serialize `powers_of_beta_times_gamma_g`.
        (self.powers_of_beta_times_gamma_g.len() as u32).write_le(&mut writer)?;
        for (key, power_of_gamma_g) in &self.powers_of_beta_times_gamma_g {
            (*key as u32).serialize_with_mode(&mut writer, mode)?;
            power_of_gamma_g.serialize_with_mode(&mut writer, mode)?;
        }
        Ok(())
    }

    fn serialized_size(&self, mode: Compress) -> usize {
        let mut size = self.file_path.serialized_size(mode);
        size += (self.powers_of_beta_times_gamma_g.len() as u32).serialized_size(mode);
        for (key, power_of_gamma_g) in &self.powers_of_beta_times_gamma_g {
            size += (*key as u32).serialized_size(mode);
            size += power_of_gamma_g.serialized_size(mode);
        }

        size
    }
}

impl<E: PairingEngine> Valid for PowersOfG<E> {
    fn check(&self) -> Result<(), SerializationError> {
        self.powers_of_beta_times_gamma_g.check()
    }
}

impl<E: PairingEngine> CanonicalDeserialize for PowersOfG<E> {
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        let file_path: String = bincode::deserialize_from(&mut reader).unwrap();

        // Deserialize `powers_of_beta_times_gamma_g`.
        let powers_of_gamma_g_num_elements: u32 =
            CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?;
        let mut keys = Vec::with_capacity(powers_of_gamma_g_num_elements as usize);
        let mut values = Vec::with_capacity(powers_of_gamma_g_num_elements as usize);
        for _ in 0..powers_of_gamma_g_num_elements {
            let key = u32::deserialize_with_mode(&mut reader, compress, validate)?;
            let power_of_gamma_g = E::G1Affine::deserialize_with_mode(&mut reader, compress, Validate::No)?;
            keys.push(key as usize);
            values.push(power_of_gamma_g);
        }
        if validate == Validate::Yes {
            E::G1Affine::batch_check(values.iter())?;
        }
        let powers_of_beta_times_gamma_g = keys.into_iter().zip(values).collect();

        let mut powers = PowersOfG::new(PathBuf::from(file_path)).unwrap();
        powers.powers_of_beta_times_gamma_g = powers_of_beta_times_gamma_g;
        Ok(powers)
    }
}
