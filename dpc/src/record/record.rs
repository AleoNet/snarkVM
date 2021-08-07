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

use crate::{Address, Parameters, Payload, PrivateKey, ProgramScheme, RecordError, RecordScheme};
use snarkvm_algorithms::traits::{CommitmentScheme, SignatureScheme, CRH, PRF};
use snarkvm_utilities::{to_bytes_le, variable_length_integer::*, FromBytes, ToBytes, UniformRand};

use rand::{CryptoRng, Rng};
use std::{
    fmt,
    io::{Read, Result as IoResult, Write},
    str::FromStr,
};

fn default_program_id<C: CRH>() -> Vec<u8> {
    C::Output::default().to_bytes_le().unwrap()
}

#[derive(Derivative)]
#[derivative(
    Default(bound = "C: Parameters"),
    Debug(bound = "C: Parameters"),
    Clone(bound = "C: Parameters"),
    PartialEq(bound = "C: Parameters"),
    Eq(bound = "C: Parameters")
)]
pub struct Record<C: Parameters> {
    #[derivative(Default(value = "default_program_id::<C::ProgramCircuitIDCRH>()"))]
    pub(crate) program_id: Vec<u8>,
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
    pub fn new_noop_input<R: Rng + CryptoRng>(
        // TODO (howardwu): TEMPORARY - `noop_program: &dyn ProgramScheme<C>` will be removed when `DPC::setup` and `DPC::load` are refactored.
        noop_program: &dyn ProgramScheme<C>,
        owner: Address<C>,
        rng: &mut R,
    ) -> Result<Self, RecordError> {
        Self::new_input(
            noop_program,
            owner,
            true,
            0,
            Payload::default(),
            C::serial_number_nonce_crh().hash(&rng.gen::<[u8; 32]>())?,
            rng,
        )
    }

    /// Returns a new noop output record.
    pub fn new_noop_output<R: Rng + CryptoRng>(
        // TODO (howardwu): TEMPORARY - `noop_program: &dyn ProgramScheme<C>` will be removed when `DPC::setup` and `DPC::load` are refactored.
        noop_program: &dyn ProgramScheme<C>,
        owner: Address<C>,
        position: u8,
        joint_serial_numbers: Vec<u8>,
        rng: &mut R,
    ) -> Result<Self, RecordError> {
        Self::new_output(
            noop_program,
            owner,
            true,
            0,
            Payload::default(),
            position,
            joint_serial_numbers,
            rng,
        )
    }

    /// Returns a new input record.
    #[allow(clippy::too_many_arguments)]
    pub fn new_input<R: Rng + CryptoRng>(
        program: &dyn ProgramScheme<C>,
        owner: Address<C>,
        is_dummy: bool,
        value: u64,
        payload: Payload,
        serial_number_nonce: C::SerialNumberNonce,
        rng: &mut R,
    ) -> Result<Self, RecordError> {
        // Sample a new record commitment randomness.
        let commitment_randomness = <C::RecordCommitmentScheme as CommitmentScheme>::Randomness::rand(rng);

        Self::from(
            &program.program_id().to_bytes_le()?,
            owner,
            is_dummy,
            value,
            payload,
            serial_number_nonce,
            commitment_randomness,
        )
    }

    /// Returns a new output record.
    #[allow(clippy::too_many_arguments)]
    pub fn new_output<R: Rng + CryptoRng>(
        program: &dyn ProgramScheme<C>,
        owner: Address<C>,
        is_dummy: bool,
        value: u64,
        payload: Payload,
        position: u8,
        joint_serial_numbers: Vec<u8>,
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
            &program.program_id().to_bytes_le()?,
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
        program_id: &Vec<u8>,
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
            program_id: program_id.clone(),
            owner,
            is_dummy,
            value,
            payload,
            serial_number_nonce,
            commitment,
            commitment_randomness,
        })
    }

    // TODO (howardwu) - Change the private_key input to a signature_public_key.
    pub fn to_serial_number(
        &self,
        private_key: &PrivateKey<C>,
    ) -> Result<
        (
            C::AccountSignaturePublicKey,
            <C::AccountSignatureScheme as SignatureScheme>::Randomizer,
        ),
        RecordError,
    > {
        let timer = start_timer!(|| "Generate serial number");

        // TODO (howardwu) - Implement after removing parameters from the inputs.
        // // Check that the private key corresponds with the owner of the record.
        // if self.owner != &Address::<C>::from_private_key(private_key)? {
        //     return Err(RecordError::IncorrectPrivateKey);
        // }

        // Compute the serial number.
        let seed = FromBytes::read_le(to_bytes_le!(&private_key.sk_prf)?.as_slice())?;
        let input = FromBytes::read_le(to_bytes_le!(self.serial_number_nonce)?.as_slice())?;
        let randomizer = FromBytes::from_bytes_le(&C::PRF::evaluate(&seed, &input)?.to_bytes_le()?)?;
        let serial_number = C::account_signature_scheme().randomize_public_key(&private_key.pk_sig()?, &randomizer)?;

        end_timer!(timer);
        Ok((serial_number, randomizer))
    }
}

impl<C: Parameters> RecordScheme for Record<C> {
    type Commitment = C::RecordCommitment;
    type CommitmentRandomness = <C::RecordCommitmentScheme as CommitmentScheme>::Randomness;
    type Owner = Address<C>;
    type Payload = Payload;
    type SerialNumber = C::AccountSignaturePublicKey;
    type SerialNumberNonce = C::SerialNumberNonce;

    fn program_id(&self) -> &[u8] {
        &self.program_id
    }

    fn owner(&self) -> &Self::Owner {
        &self.owner
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
        variable_length_integer(self.program_id.len() as u64).write_le(&mut writer)?;
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
        let program_id_size: usize = read_variable_length_integer(&mut reader)?;
        let mut program_id = Vec::with_capacity(program_id_size);
        for _ in 0..program_id_size {
            let byte: u8 = FromBytes::read_le(&mut reader)?;
            program_id.push(byte);
        }

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
