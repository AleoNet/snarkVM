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

use snarkvm_utilities::{FromBytes, ToBytes};

use std::hash::Hash;

pub trait RecordScheme: Default + FromBytes + ToBytes {
    type Owner;
    type Commitment: FromBytes + ToBytes;
    type CommitmentRandomness;
    type Payload;
    type SerialNumberNonce;
    type SerialNumber: Clone + Eq + Hash + FromBytes + ToBytes;
    type Value: FromBytes + ToBytes;

    /// Returns the record owner.
    fn owner(&self) -> &Self::Owner;

    /// Returns whether or not the record is dummy.
    fn is_dummy(&self) -> bool;

    /// Returns the record payload.
    fn payload(&self) -> &Self::Payload;

    /// Returns the birth program id of this record.
    fn birth_program_id(&self) -> &[u8];

    /// Returns the death program id of this record.
    fn death_program_id(&self) -> &[u8];

    /// Returns the nonce used for the serial number.
    fn serial_number_nonce(&self) -> &Self::SerialNumberNonce;

    /// Returns the randomness used for the serial number nonce.
    fn serial_number_nonce_randomness(&self) -> &Option<[u8; 32]>;

    fn position(&self) -> &Option<u8>;

    /// Returns the commitment of this record.
    fn commitment(&self) -> Self::Commitment;

    /// Returns the randomness used for the commitment.
    fn commitment_randomness(&self) -> Self::CommitmentRandomness;

    /// Returns the record value.
    fn value(&self) -> Self::Value;
}
