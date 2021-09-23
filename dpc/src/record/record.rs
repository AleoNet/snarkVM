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

use crate::{Address, ComputeKey, Network, Payload, RecordError, RecordScheme};
use snarkvm_algorithms::traits::{CommitmentScheme, PRF};
use snarkvm_utilities::{to_bytes_le, FromBytes, ToBytes, UniformRand};

use rand::{CryptoRng, Rng};
use std::{
    fmt,
    io::{Read, Result as IoResult, Write},
    str::FromStr,
};

#[derive(Derivative)]
#[derivative(
    Default(bound = "N: Network"),
    Debug(bound = "N: Network"),
    Clone(bound = "N: Network"),
    PartialEq(bound = "N: Network"),
    Eq(bound = "N: Network")
)]
pub struct Record<N: Network> {
    owner: Address<N>,
    // TODO (raychu86) use AleoAmount which will guard the value range
    value: u64,
    payload: Payload,
    program_id: N::ProgramID,
    serial_number_nonce: N::SerialNumber,
    commitment_randomness: <N::CommitmentScheme as CommitmentScheme>::Randomness,
    commitment: N::Commitment,
}

impl<N: Network> Record<N> {
    /// Returns a new noop input record.
    pub fn new_noop_input<R: Rng + CryptoRng>(owner: Address<N>, rng: &mut R) -> Result<Self, RecordError> {
        Self::new_input(
            owner,
            0,
            Payload::default(),
            N::noop_program_id(),
            UniformRand::rand(rng),
            UniformRand::rand(rng),
        )
    }

    /// Returns a new input record.
    pub fn new_input(
        owner: Address<N>,
        value: u64,
        payload: Payload,
        program_id: N::ProgramID,
        serial_number_nonce: N::SerialNumber,
        commitment_randomness: <N::CommitmentScheme as CommitmentScheme>::Randomness,
    ) -> Result<Self, RecordError> {
        Self::from(
            owner,
            value,
            payload,
            program_id,
            serial_number_nonce,
            commitment_randomness,
        )
    }

    /// Returns a new noop output record.
    pub fn new_noop_output<R: Rng + CryptoRng>(
        owner: Address<N>,
        serial_number_nonce: N::SerialNumber,
        rng: &mut R,
    ) -> Result<Self, RecordError> {
        Self::new_output(
            owner,
            0,
            Payload::default(),
            N::noop_program_id(),
            serial_number_nonce,
            rng,
        )
    }

    /// Returns a new output record.
    pub fn new_output<R: Rng + CryptoRng>(
        owner: Address<N>,
        value: u64,
        payload: Payload,
        program_id: N::ProgramID,
        serial_number_nonce: N::SerialNumber,
        rng: &mut R,
    ) -> Result<Self, RecordError> {
        Self::from(
            owner,
            value,
            payload,
            program_id,
            serial_number_nonce,
            UniformRand::rand(rng),
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub fn from(
        owner: Address<N>,
        value: u64,
        payload: Payload,
        program_id: N::ProgramID,
        serial_number_nonce: N::SerialNumber,
        commitment_randomness: <N::CommitmentScheme as CommitmentScheme>::Randomness,
    ) -> Result<Self, RecordError> {
        // Determine if the record is a dummy.
        let is_dummy = value == 0 && payload.is_empty() && program_id == N::noop_program_id();

        // Total = 32 + 1 + 8 + 128 + 48 + 32 = 249 bytes
        let commitment_input = to_bytes_le![
            owner,               // 256 bits = 32 bytes
            is_dummy,            // 1 bit = 1 byte
            value,               // 64 bits = 8 bytes
            payload,             // 1024 bits = 128 bytes
            program_id,          // 384 bits = 48 bytes
            serial_number_nonce  // 256 bits = 32 bytes
        ]?;

        // Compute the record commitment.
        let commitment = N::commitment_scheme().commit(&commitment_input, &commitment_randomness)?;

        Ok(Self {
            program_id,
            owner,
            value,
            payload,
            serial_number_nonce,
            commitment_randomness,
            commitment,
        })
    }

    pub fn to_serial_number(&self, compute_key: &ComputeKey<N>) -> Result<N::SerialNumber, RecordError> {
        // Check that the compute key corresponds with the owner of the record.
        if self.owner != Address::<N>::from_compute_key(compute_key)? {
            return Err(RecordError::IncorrectComputeKey);
        }

        // TODO (howardwu): CRITICAL - Review the translation from scalar to base field of `sk_prf`.
        // Compute the serial number.
        let seed = FromBytes::read_le(&compute_key.sk_prf().to_bytes_le()?[..])?;
        let input = &vec![self.serial_number_nonce.clone()];
        let serial_number = N::SerialNumberPRF::evaluate(&seed, input)?;

        Ok(serial_number)
    }
}

impl<N: Network> RecordScheme for Record<N> {
    type Commitment = N::Commitment;
    type CommitmentRandomness = <N::CommitmentScheme as CommitmentScheme>::Randomness;
    type Owner = Address<N>;
    type Payload = Payload;
    type ProgramID = N::ProgramID;
    type SerialNumberNonce = N::SerialNumber;

    fn is_dummy(&self) -> bool {
        self.value == 0 && self.payload.is_empty() && self.program_id == N::noop_program_id()
    }

    fn owner(&self) -> Self::Owner {
        self.owner
    }

    fn value(&self) -> u64 {
        self.value
    }

    fn payload(&self) -> &Self::Payload {
        &self.payload
    }

    fn program_id(&self) -> Self::ProgramID {
        self.program_id
    }

    fn serial_number_nonce(&self) -> &Self::SerialNumberNonce {
        &self.serial_number_nonce
    }

    fn commitment_randomness(&self) -> Self::CommitmentRandomness {
        self.commitment_randomness.clone()
    }

    fn commitment(&self) -> Self::Commitment {
        self.commitment.clone()
    }
}

impl<N: Network> ToBytes for Record<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.owner.write_le(&mut writer)?;
        self.value.write_le(&mut writer)?;
        self.payload.write_le(&mut writer)?;
        self.program_id.write_le(&mut writer)?;
        self.serial_number_nonce.write_le(&mut writer)?;
        self.commitment_randomness.write_le(&mut writer)
    }
}

impl<N: Network> FromBytes for Record<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let owner: Address<N> = FromBytes::read_le(&mut reader)?;
        let value: u64 = FromBytes::read_le(&mut reader)?;
        let payload: Payload = FromBytes::read_le(&mut reader)?;
        let program_id: N::ProgramID = FromBytes::read_le(&mut reader)?;
        let serial_number_nonce: N::SerialNumber = FromBytes::read_le(&mut reader)?;
        let commitment_randomness: <N::CommitmentScheme as CommitmentScheme>::Randomness =
            FromBytes::read_le(&mut reader)?;

        Ok(Self::from(
            owner,
            value,
            payload,
            program_id,
            serial_number_nonce,
            commitment_randomness,
        )?)
    }
}

impl<N: Network> FromStr for Record<N> {
    type Err = RecordError;

    fn from_str(record: &str) -> Result<Self, Self::Err> {
        Ok(Self::read_le(&hex::decode(record)?[..])?)
    }
}

impl<N: Network> fmt::Display for Record<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            hex::encode(to_bytes_le![self].expect("serialization to bytes failed"))
        )
    }
}
