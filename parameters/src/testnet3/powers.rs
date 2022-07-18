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

use anyhow::{anyhow, bail, ensure, Result};
use itertools::Itertools;
use std::{collections::BTreeMap, io::BufReader};

const DEGREE_15: usize = 1 << 15;
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

/// The maximum degree supported by the SRS.
const MAXIMUM_DEGREE: usize = DEGREE_28;

/// Number of powers contained in `UNIVERSAL_SRS_GAMMA`.
const NUM_UNIVERSAL_SRS_GAMMA: usize = 84;

lazy_static::lazy_static! {
    static ref UNIVERSAL_SRS_15: Vec<u8> = Degree15::load_bytes().expect("Failed to load universal SRS of degree 15");
    static ref UNIVERSAL_SRS_GAMMA: Vec<u8> = Gamma::load_bytes().expect("Failed to load universal SRS gamma powers");
}

/// A vector of powers of beta G.
#[derive(Debug)]
pub struct PowersOfG<E: PairingEngine> {
    /// A boolean indicator if the powers were from a setup.
    is_setup: bool,
    /// The number of group elements in `powers_of_beta_g`.
    current_degree: usize,
    /// Group elements of form `[G, \beta * G, \beta^2 * G, ..., \beta^{d} G]`.
    powers_of_beta_g: Vec<E::G1Affine>,
    /// Group elements of form `{ \beta^i \gamma G }`, where `i` is from 0 to `degree`, used for hiding.
    powers_of_beta_times_gamma_g: BTreeMap<usize, E::G1Affine>,
}

impl<E: PairingEngine> PowersOfG<E> {
    /// Initializes a new instance of the powers.
    pub fn setup(
        powers_of_beta_g: Vec<E::G1Affine>,
        powers_of_beta_times_gamma_g: BTreeMap<usize, E::G1Affine>,
    ) -> Result<Self> {
        // Initialize the powers.
        let powers = Self {
            is_setup: true,
            current_degree: powers_of_beta_g.len(),
            powers_of_beta_g,
            powers_of_beta_times_gamma_g,
        };
        // Return the powers.
        Ok(powers)
    }

    /// Initializes an existing instance of the powers.
    pub fn load() -> Result<Self> {
        // Initialize a `BufReader`.
        let mut reader = BufReader::new(&UNIVERSAL_SRS_15[..]);
        // Deserialize the group elements.
        let powers_of_beta_g = (0..DEGREE_15)
            .map(|_| E::G1Affine::read_le(&mut reader))
            // .map(|_| E::G1Affine::deserialize_with_mode(&mut reader, Compress::No, Validate::No))
            .collect::<Result<Vec<_>, _>>()?;
        // Ensure the number of elements is correct.
        ensure!(powers_of_beta_g.len() == DEGREE_15, "Incorrect number of powers in the recovered SRS");

        // Initialize the powers.
        let powers = Self {
            is_setup: false,
            current_degree: DEGREE_15,
            powers_of_beta_g,
            powers_of_beta_times_gamma_g: Self::regenerate_powers_of_beta_times_gamma_g(DEGREE_15)?,
        };
        // Return the powers.
        Ok(powers)
    }

    /// Returns the power of beta times G specified by `target_power`.
    pub fn power_of_beta_g(&mut self, target_power: usize) -> Result<E::G1Affine> {
        // Ensure the powers exist, and download the missing powers if necessary.
        if target_power >= self.current_degree {
            self.download_up_to(target_power)?;
        }
        // Return the power.
        self.powers_of_beta_g.get(target_power).copied().ok_or_else(|| anyhow!("Failed to get power of beta G"))
    }

    /// Slices the underlying file to return a vector of affine elements between `lower` and `upper`.
    pub fn powers_of_beta_g(&mut self, lower: usize, upper: usize) -> Result<Vec<E::G1Affine>> {
        // Ensure the lower power is less than the upper power.
        ensure!(lower < upper, "Lower power must be less than upper power");
        // Ensure the powers exist, and download the missing powers if necessary.
        if upper >= self.current_degree {
            self.download_up_to(upper)?;
        }
        // Return the powers.
        Ok(self.powers_of_beta_g[lower..upper].to_vec())
    }

    /// Returns the powers of beta * gamma G.
    pub fn powers_times_gamma_g(&self) -> &BTreeMap<usize, E::G1Affine> {
        &self.powers_of_beta_times_gamma_g
    }

    /// Return the number of current powers of G.
    pub fn degree(&self) -> usize {
        self.current_degree
    }

    /// This method downloads the universal SRS powers up to the `next_power_of_two(target_degree)`,
    /// and updates `Self` in place with the new powers.
    pub fn download_up_to(&mut self, target_degree: usize) -> Result<()> {
        // Initialize the first degree to download.
        let mut next_degree = std::cmp::max(self.current_degree.next_power_of_two(), DEGREE_16);

        // Determine the degrees to download.
        let mut download_queue = Vec::new();
        // Download the powers until the target degree is reached.
        while next_degree <= target_degree && next_degree <= MAXIMUM_DEGREE {
            // Append the next degree to the download queue.
            download_queue.push(next_degree);
            // Update the next degree.
            next_degree *= 2;
        }

        // If the `target_degree` exceeds the current `degree`, proceed to download the new powers.
        if !download_queue.is_empty() {
            // If the powers are from a setup, then it cannot download more powers.
            if self.is_setup {
                bail!(
                    "Cannot download more than {} powers for this setup (attempted {})",
                    self.degree(),
                    target_degree
                );
            }

            for degree in &download_queue {
                println!("Downloading SRS of degree {}", degree);

                // Download the universal SRS powers.
                let (number_of_elements, additional_bytes) = match *degree {
                    DEGREE_16 => (DEGREE_15, Degree16::load_bytes()?),
                    DEGREE_17 => (DEGREE_16, Degree17::load_bytes()?),
                    DEGREE_18 => (DEGREE_17, Degree18::load_bytes()?),
                    DEGREE_19 => (DEGREE_18, Degree19::load_bytes()?),
                    DEGREE_20 => (DEGREE_19, Degree20::load_bytes()?),
                    DEGREE_21 => (DEGREE_20, Degree21::load_bytes()?),
                    DEGREE_22 => (DEGREE_21, Degree22::load_bytes()?),
                    DEGREE_23 => (DEGREE_22, Degree23::load_bytes()?),
                    DEGREE_24 => (DEGREE_23, Degree24::load_bytes()?),
                    DEGREE_25 => (DEGREE_24, Degree25::load_bytes()?),
                    DEGREE_26 => (DEGREE_25, Degree26::load_bytes()?),
                    DEGREE_27 => (DEGREE_26, Degree27::load_bytes()?),
                    DEGREE_28 => (DEGREE_27, Degree28::load_bytes()?),
                    _ => bail!("Cannot download an invalid degree of '{degree}'"),
                };

                // Initialize a `BufReader`.
                let mut reader = BufReader::new(&additional_bytes[..]);
                // Deserialize the group elements.
                let additional_powers = (0..number_of_elements)
                    .map(|_| E::G1Affine::read_le(&mut reader))
                    // .map(|_| E::G1Affine::deserialize_with_mode(&mut reader, Compress::No, Validate::No))
                    .collect::<Result<Vec<_>, _>>()?;

                // Extend the powers.
                self.powers_of_beta_g.extend(&additional_powers);
                // Update the `degree`.
                self.current_degree = self.powers_of_beta_g.len();
            }
            // Regenerate the powers of beta * gamma G.
            self.powers_of_beta_times_gamma_g = Self::regenerate_powers_of_beta_times_gamma_g(self.current_degree)?;
        }
        Ok(())
    }
}

impl<E: PairingEngine> PowersOfG<E> {
    fn regenerate_powers_of_beta_times_gamma_g(current_degree: usize) -> Result<BTreeMap<usize, E::G1Affine>> {
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
            if current_degree - 1 > (1 << i) {
                let powers = powers.into_iter().collect::<Vec<_>>();
                alpha_tau_powers_g1.insert(current_degree - 1 - (1 << i) + 2, *powers[0]);
                alpha_tau_powers_g1.insert(current_degree - 1 - (1 << i) + 3, *powers[1]);
                alpha_tau_powers_g1.insert(current_degree - 1 - (1 << i) + 4, *powers[2]);
            }
        });
        Ok(alpha_tau_powers_g1)
    }
}

impl<E: PairingEngine> FromBytes for PowersOfG<E> {
    /// Reads the powers from the buffer.
    fn read_le<R: Read>(reader: R) -> std::io::Result<Self> {
        Self::deserialize_with_mode(reader, Compress::No, Validate::No).map_err(|e| e.into())
    }
}

impl<E: PairingEngine> ToBytes for PowersOfG<E> {
    /// Writes the powers to the buffer.
    fn write_le<W: Write>(&self, writer: W) -> std::io::Result<()> {
        self.serialize_with_mode(writer, Compress::No).map_err(|e| e.into())
    }
}

impl<E: PairingEngine> CanonicalSerialize for PowersOfG<E> {
    /// Serializes the powers to the buffer.
    fn serialize_with_mode<W: Write>(&self, mut writer: W, mode: Compress) -> Result<(), SerializationError> {
        // Serialize `is_setup`.
        self.is_setup.serialize_with_mode(&mut writer, mode)?;

        // If the powers are from a setup, then serialize each component.
        if self.is_setup {
            // Serialize the number of powers of beta G.
            (self.current_degree as u32).serialize_with_mode(&mut writer, mode)?;
            // Serialize the powers of beta G.
            for power_of_beta_g in &self.powers_of_beta_g {
                power_of_beta_g.serialize_with_mode(&mut writer, mode)?;
            }

            // Serialize the number of powers of beta * gamma G.
            (self.powers_of_beta_times_gamma_g.len() as u32).write_le(&mut writer)?;
            // Serialize the powers of beta * gamma G.
            for (index, power_of_beta_times_gamma_g) in &self.powers_of_beta_times_gamma_g {
                // Serialize the index.
                (*index as u32).serialize_with_mode(&mut writer, mode)?;
                // Serialize the power of beta * gamma G.
                power_of_beta_times_gamma_g.serialize_with_mode(&mut writer, mode)?;
            }
        }
        Ok(())
    }

    /// Returns the number of bytes required to serialize the powers.
    fn serialized_size(&self, mode: Compress) -> usize {
        // Initialize the size.
        let mut size = 1;
        // If the powers are from a setup, then serialize each component.
        if self.is_setup {
            size += (self.current_degree as u32).serialized_size(mode);
            for power_of_beta_g in &self.powers_of_beta_g {
                size += power_of_beta_g.serialized_size(mode);
            }

            size += (self.powers_of_beta_times_gamma_g.len() as u32).serialized_size(mode);
            for (index, power_of_beta_times_gamma_g) in &self.powers_of_beta_times_gamma_g {
                size += (*index as u32).serialized_size(mode);
                size += power_of_beta_times_gamma_g.serialized_size(mode);
            }
        }
        // Return the size.
        size
    }
}

impl<E: PairingEngine> CanonicalDeserialize for PowersOfG<E> {
    /// Deserializes the powers from the buffer.
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        // Deserialize `is_setup`.
        let is_setup = bool::deserialize_with_mode(&mut reader, compress, validate)?;

        // If the powers are from a setup, then deserialize each component.
        if is_setup {
            // Deserialize the number of powers of beta G.
            let degree = u32::deserialize_with_mode(&mut reader, compress, validate)?;
            // Deserialize the powers of beta G.
            let powers_of_beta_g = (0..degree)
                .map(|_| {
                    // Deserialize the group element.
                    E::G1Affine::deserialize_with_mode(&mut reader, compress, Validate::No)
                    // E::G1Affine::read_le(&mut reader)
                })
                .collect::<Result<Vec<_>, _>>()?;

            // Deserialize the number of powers of beta * gamma G.
            let number_of_powers = u32::deserialize_with_mode(&mut reader, compress, validate)?;
            // Deserialize the powers of beta * gamma G.
            let powers_of_beta_times_gamma_g = (0..number_of_powers)
                .map(|_| {
                    // Deserialize the index.
                    let index = u32::deserialize_with_mode(&mut reader, compress, validate)?;
                    // Deserialize the group element.
                    let element = E::G1Affine::deserialize_with_mode(&mut reader, compress, Validate::No)?;
                    // Return the index and the group element.
                    Ok::<_, SerializationError>((index as usize, element))
                })
                .collect::<Result<BTreeMap<_, _>, _>>()?;

            // If the validation is enabled, check that the group elements are on the curve.
            if validate == Validate::Yes {
                // Perform a batch check over the elements.
                E::G1Affine::batch_check(powers_of_beta_g.iter())?;
                // Perform a batch check over the elements.
                E::G1Affine::batch_check(powers_of_beta_times_gamma_g.values())?;
            }
            // Return the powers.
            Ok(Self::setup(powers_of_beta_g, powers_of_beta_times_gamma_g)?)
        } else {
            Ok(Self::load()?)
        }
    }
}

impl<E: PairingEngine> Valid for PowersOfG<E> {
    /// Checks that the powers are valid.
    fn check(&self) -> Result<(), SerializationError> {
        self.powers_of_beta_g.check()?;
        self.powers_of_beta_times_gamma_g.check()
    }
}
