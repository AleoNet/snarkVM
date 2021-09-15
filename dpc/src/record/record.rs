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

use crate::{Address, ComputeKey, Parameters, Payload, ProgramScheme, RecordError, RecordScheme};
use snarkvm_algorithms::{
    merkle_tree::MerkleTreeDigest,
    traits::{CommitmentScheme, CRH, PRF},
};
use snarkvm_utilities::{to_bytes_le, FromBytes, ToBytes, UniformRand};

use rand::{CryptoRng, Rng};
use std::{
    fmt,
    io::{Read, Result as IoResult, Write},
    str::FromStr,
};

#[derive(Derivative)]
#[derivative(
    Default(bound = "C: Parameters"),
    Debug(bound = "C: Parameters"),
    Clone(bound = "C: Parameters"),
    PartialEq(bound = "C: Parameters"),
    Eq(bound = "C: Parameters")
)]
pub struct Record<C: Parameters> {
    pub(crate) program_id: MerkleTreeDigest<C::ProgramCircuitTreeParameters>,
    pub(crate) owner: Address<C>,
    pub(crate) is_dummy: bool,
    // TODO (raychu86) use AleoAmount which will guard the value range
    pub(crate) value: u64,
    pub(crate) payload: Payload,
    pub(crate) serial_number_nonce: C::SerialNumberNonce,
    pub(crate) commitment: C::RecordCommitment,
    pub(crate) commitment_randomness: <C::RecordCommitmentScheme as CommitmentScheme>::Randomness,
}

impl<C: Parameters> Record<C> {
    /// Returns a new noop input record.
    pub fn new_noop_input<R: Rng + CryptoRng>(owner: Address<C>, rng: &mut R) -> Result<Self, RecordError> {
        // Sample a new record commitment randomness.
        let commitment_randomness = <C::RecordCommitmentScheme as CommitmentScheme>::Randomness::rand(rng);

        Self::new_input(
            C::noop_program().program_id(),
            owner,
            true,
            0,
            Payload::default(),
            C::serial_number_nonce_crh().hash(&rng.gen::<[u8; 32]>())?,
            commitment_randomness,
        )
    }

    /// Returns a new input record.
    #[allow(clippy::too_many_arguments)]
    pub fn new_input(
        program_id: MerkleTreeDigest<C::ProgramCircuitTreeParameters>,
        owner: Address<C>,
        is_dummy: bool,
        value: u64,
        payload: Payload,
        serial_number_nonce: C::SerialNumberNonce,
        commitment_randomness: <C::RecordCommitmentScheme as CommitmentScheme>::Randomness,
    ) -> Result<Self, RecordError> {
        Self::from(
            program_id,
            owner,
            is_dummy,
            value,
            payload,
            serial_number_nonce,
            commitment_randomness,
        )
    }

    /// Returns a new noop output record.
    pub fn new_noop_output<R: Rng + CryptoRng>(
        owner: Address<C>,
        position: u8,
        joint_serial_numbers: &Vec<u8>,
        rng: &mut R,
    ) -> Result<Self, RecordError> {
        Self::new_output(
            C::noop_program().program_id(),
            owner,
            true,
            0,
            Payload::default(),
            position,
            joint_serial_numbers,
            rng,
        )
    }

    /// Returns a new output record.
    #[allow(clippy::too_many_arguments)]
    pub fn new_output<R: Rng + CryptoRng>(
        program_id: MerkleTreeDigest<C::ProgramCircuitTreeParameters>,
        owner: Address<C>,
        is_dummy: bool,
        value: u64,
        payload: Payload,
        position: u8,
        joint_serial_numbers: &Vec<u8>,
        rng: &mut R,
    ) -> Result<Self, RecordError> {
        // Ensure the output record position is valid.
        if (position as usize) < C::NUM_INPUT_RECORDS {
            return Err(RecordError::InvalidOutputPosition(position));
        }

        // Compute the serial number nonce.
        let serial_number_nonce = C::serial_number_nonce_crh().hash(&to_bytes_le![position, joint_serial_numbers]?)?;
        // Sample a new record commitment randomness.
        let commitment_randomness = <C::RecordCommitmentScheme as CommitmentScheme>::Randomness::rand(rng);

        Self::from(
            program_id,
            owner,
            is_dummy,
            value,
            payload,
            serial_number_nonce,
            commitment_randomness,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub fn from(
        program_id: MerkleTreeDigest<C::ProgramCircuitTreeParameters>,
        owner: Address<C>,
        is_dummy: bool,
        value: u64,
        payload: Payload,
        serial_number_nonce: C::SerialNumberNonce,
        commitment_randomness: <C::RecordCommitmentScheme as CommitmentScheme>::Randomness,
    ) -> Result<Self, RecordError> {
        // Total = 48 + 32 + 1 + 8 + 128 + 32 = 249 bytes
        let commitment_input = to_bytes_le![
            program_id,          // 384 bits = 48 bytes
            owner,               // 256 bits = 32 bytes
            is_dummy,            // 1 bit = 1 byte
            value,               // 64 bits = 8 bytes
            payload,             // 1024 bits = 128 bytes
            serial_number_nonce  // 256 bits = 32 bytes
        ]?;

        // Compute the record commitment.
        let commitment = C::record_commitment_scheme().commit(&commitment_input, &commitment_randomness)?;

        Ok(Self {
            program_id,
            owner,
            is_dummy,
            value,
            payload,
            serial_number_nonce,
            commitment,
            commitment_randomness,
        })
    }

    pub fn to_serial_number(&self, compute_key: &ComputeKey<C>) -> Result<C::SerialNumber, RecordError> {
        // Check that the compute key corresponds with the owner of the record.
        if self.owner != Address::<C>::from_compute_key(compute_key)? {
            return Err(RecordError::IncorrectComputeKey);
        }

        // TODO (howardwu): CRITICAL - Review the translation from scalar to base field of `sk_prf`.
        // Compute the serial number.
        let seed = FromBytes::read_le(&compute_key.sk_prf().to_bytes_le()?[..])?;
        let input = &vec![self.serial_number_nonce.clone()];
        let serial_number = C::SerialNumberPRF::evaluate(&seed, input)?;

        Ok(serial_number)
    }
}

impl<C: Parameters> RecordScheme for Record<C> {
    type Commitment = C::RecordCommitment;
    type CommitmentRandomness = <C::RecordCommitmentScheme as CommitmentScheme>::Randomness;
    type Owner = Address<C>;
    type Payload = Payload;
    type ProgramID = MerkleTreeDigest<C::ProgramCircuitTreeParameters>;
    type SerialNumber = C::SerialNumber;
    type SerialNumberNonce = C::SerialNumberNonce;

    fn program_id(&self) -> Self::ProgramID {
        self.program_id
    }

    fn owner(&self) -> Self::Owner {
        self.owner
    }

    fn is_dummy(&self) -> bool {
        self.is_dummy
    }

    fn value(&self) -> u64 {
        self.value
    }

    fn payload(&self) -> &Self::Payload {
        &self.payload
    }

    fn serial_number_nonce(&self) -> &Self::SerialNumberNonce {
        &self.serial_number_nonce
    }

    fn commitment(&self) -> Self::Commitment {
        self.commitment.clone()
    }

    fn commitment_randomness(&self) -> Self::CommitmentRandomness {
        self.commitment_randomness.clone()
    }
}

impl<C: Parameters> ToBytes for Record<C> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.program_id.write_le(&mut writer)?;
        self.owner.write_le(&mut writer)?;
        self.is_dummy.write_le(&mut writer)?;
        self.value.write_le(&mut writer)?;
        self.payload.write_le(&mut writer)?;
        self.serial_number_nonce.write_le(&mut writer)?;
        self.commitment.write_le(&mut writer)?;
        self.commitment_randomness.write_le(&mut writer)
    }
}

impl<C: Parameters> FromBytes for Record<C> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let program_id: MerkleTreeDigest<C::ProgramCircuitTreeParameters> = FromBytes::read_le(&mut reader)?;
        let owner: Address<C> = FromBytes::read_le(&mut reader)?;
        let is_dummy: bool = FromBytes::read_le(&mut reader)?;
        let value: u64 = FromBytes::read_le(&mut reader)?;
        let payload: Payload = FromBytes::read_le(&mut reader)?;
        let serial_number_nonce: C::SerialNumberNonce = FromBytes::read_le(&mut reader)?;
        let commitment: C::RecordCommitment = FromBytes::read_le(&mut reader)?;
        let commitment_randomness: <C::RecordCommitmentScheme as CommitmentScheme>::Randomness =
            FromBytes::read_le(&mut reader)?;

        Ok(Self {
            program_id,
            owner,
            is_dummy,
            value,
            payload,
            serial_number_nonce,
            commitment,
            commitment_randomness,
        })
    }
}

impl<C: Parameters> FromStr for Record<C> {
    type Err = RecordError;

    fn from_str(record: &str) -> Result<Self, Self::Err> {
        Ok(Self::read_le(&hex::decode(record)?[..])?)
    }
}

impl<C: Parameters> fmt::Display for Record<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            hex::encode(to_bytes_le![self].expect("serialization to bytes failed"))
        )
    }
}
