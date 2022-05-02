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

use anyhow::{anyhow, Result};
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

use itertools::Itertools;
use std::{
    collections::{BTreeMap, HashMap},
    fs::{File, OpenOptions},
    io::{BufReader, Seek, SeekFrom},
    path::PathBuf,
};

lazy_static::lazy_static! {
    static ref DEFAULT_PATH: PathBuf = PathBuf::from(format!("{}/.aleo/powers_of_g", std::env::var("HOME").unwrap()));
    static ref URLS: HashMap<usize, String> = {
        let mut m = HashMap::new();
        m.insert(1 << 16, String::from("https://f002.backblazeb2.com/file/aleo-snarkos/srs/powers_of_g_16"));
        m.insert(1 << 17, String::from("https://f002.backblazeb2.com/file/aleo-snarkos/srs/powers_of_g_17"));
        m.insert(1 << 18, String::from("https://f002.backblazeb2.com/file/aleo-snarkos/srs/powers_of_g_18"));
        m.insert(1 << 19, String::from("https://f002.backblazeb2.com/file/aleo-snarkos/srs/powers_of_g_19"));
        m.insert(1 << 20, String::from("https://f002.backblazeb2.com/file/aleo-snarkos/srs/powers_of_g_20"));
        m.insert(1 << 21, String::from("https://f002.backblazeb2.com/file/aleo-snarkos/srs/powers_of_g_21"));
        m.insert(1 << 22, String::from("https://f002.backblazeb2.com/file/aleo-snarkos/srs/powers_of_g_22"));
        m.insert(1 << 23, String::from("https://f002.backblazeb2.com/file/aleo-snarkos/srs/powers_of_g_23"));
        m.insert(1 << 24, String::from("https://f002.backblazeb2.com/file/aleo-snarkos/srs/powers_of_g_24"));
        m.insert(1 << 25, String::from("https://f002.backblazeb2.com/file/aleo-snarkos/srs/powers_of_g_25"));
        m.insert(1 << 26, String::from("https://f002.backblazeb2.com/file/aleo-snarkos/srs/powers_of_g_26"));
        m.insert(1 << 27, String::from("https://f002.backblazeb2.com/file/aleo-snarkos/srs/powers_of_g_27"));
        m.insert(1 << 28, String::from("https://f002.backblazeb2.com/file/aleo-snarkos/srs/powers_of_g_28"));
        m
    };
    static ref BASE_POWERS: &'static [u8] = include_bytes!("./powers_of_g_15");
    static ref POWERS_TIMES_GAMMA_G: &'static [u8] = include_bytes!("./gamma_powers");
}

// Amount of powers contained in `POWERS_TIMES_GAMMA_G`.
const NUM_POWERS_TIMES_GAMMA_G: usize = 84;

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
    /// Returns a new instance of PowersOfG, which will store its
    /// powers in a file at `file_path`.
    pub fn new(file_path: PathBuf) -> Result<Self> {
        // Open the given file, creating it if it doesn't yet exist.
        let mut file = OpenOptions::new().read(true).write(true).create(true).open(file_path.clone())?;

        // If the file is empty, let's write the base powers (up to degree 15)
        // to it.
        if file.metadata()?.len() == 0 {
            file.write_all(&BASE_POWERS)?;
        }

        let degree = file.metadata()?.len() as usize / E::G1Affine::SERIALIZED_SIZE;

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
    pub fn len(&self) -> usize {
        self.degree
    }

    /// Returns whether or not the current powers of G are empty.
    /// This file should never be empty since we always write at least
    /// up to the 15th degree, so this will always return false.
    pub fn is_empty(&self) -> bool {
        false
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
            .checked_mul(E::G1Affine::SERIALIZED_SIZE)
            .expect("attempted to index powers of G with an index greater than usize");
        self.ensure_powers_exist(index_start);

        index_start
    }

    fn ensure_powers_exist(&mut self, index: usize) {
        if index > self.file.metadata().expect("could not get powers of G metadata").len() as usize {
            let degree = index.next_power_of_two();
            self.download_up_to(degree).expect("could not download missing powers of G");
        }
    }

    fn get_degrees_to_download(&self, degree: usize) -> Vec<usize> {
        let mut degrees = vec![];
        let mut starting_degree = self.degree;
        loop {
            let next_degree_to_download = starting_degree * 2;
            degrees.push(next_degree_to_download);
            if next_degree_to_download >= degree {
                break;
            }
            starting_degree = next_degree_to_download;
        }
        degrees
    }

    /// Download the transcript up to `degree`.
    #[cfg(not(feature = "wasm"))]
    pub fn download_up_to(&mut self, degree: usize) -> Result<()> {
        println!("called download");
        let degrees_to_download = self.get_degrees_to_download(degree);
        for d in &degrees_to_download {
            println!("downloading new degree");
            if let Some(link) = URLS.get(d) {
                let mut easy = curl::easy::Easy::new();
                easy.url(link)?;
                let mut transfer = easy.transfer();
                transfer.write_function(|data| {
                    self.file.seek(SeekFrom::End(0)).unwrap();
                    self.file.write_all(data).unwrap();
                    Ok(data.len())
                })?;
                transfer.perform()?;
            } else {
                return Err(anyhow!("incorrect degree selected - {}", degree));
            }
        }

        self.degree = *degrees_to_download.last().unwrap();
        self.regenerate_powers_of_beta_times_gamma_g();

        Ok(())
    }

    /// Download the transcript up to `degree`.
    #[cfg(feature = "wasm")]
    pub fn download_up_to(&mut self, degree: usize) -> Result<()> {
        let degrees_to_download = self.get_degrees_to_download(degree);
        for d in &degrees_to_download {
            if let Some(link) = URLS.get(d) {
                let buffer = alloc::sync::Arc::new(parking_lot::RwLock::new(vec![]));
                let url = String::from(link);

                // NOTE(julesdesmit): I'm leaking memory here so that I can get a
                // static reference to the url, which is needed to pass it into
                // the local thread which downloads the file.
                let buffer_clone = alloc::sync::Arc::downgrade(&buffer);
                // NOTE(julesdesmit): We spawn a local thread here in order to be
                // able to accommodate the async syntax from reqwest.
                wasm_bindgen_futures::spawn_local(async move {
                    let content = reqwest::get(url).await.unwrap().text().await.unwrap();

                    let buffer = buffer_clone.upgrade().unwrap();
                    buffer.write().extend_from_slice(content.as_bytes());
                    drop(buffer);
                });
                // Recover the bytes.
                let buffer = alloc::sync::Arc::try_unwrap(buffer).unwrap();
                let buffer = buffer.write().clone();
                self.file.seek(SeekFrom::End(0))?;
                self.file.write_all(&buffer)?;
            } else {
                return Err(anyhow!("incorrect degree selected - {}", degree));
            }
        }

        self.degree = *degrees_to_download.last().unwrap();
        self.regenerate_powers_of_beta_times_gamma_g();

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
            if self.len() - 1 > (1 << i) {
                let c = c.into_iter().collect::<Vec<_>>();
                alpha_tau_powers_g1.insert(self.len() - 1 - (1 << i) + 2, *c[0]);
                alpha_tau_powers_g1.insert(self.len() - 1 - (1 << i) + 3, *c[1]);
                alpha_tau_powers_g1.insert(self.len() - 1 - (1 << i) + 4, *c[2]);
            }
        });

        self.powers_of_beta_times_gamma_g = alpha_tau_powers_g1;
    }

    pub fn get_powers_times_gamma_g(&self) -> &BTreeMap<usize, E::G1Affine> {
        &self.powers_of_beta_times_gamma_g
    }
}
