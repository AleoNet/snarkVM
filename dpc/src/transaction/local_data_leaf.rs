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

use crate::{DPCError, Parameters, Transaction, TransactionScheme};
use snarkvm_algorithms::prelude::*;
use snarkvm_utilities::{to_bytes_le, FromBytes, ToBytes};

use std::io::{Read, Result as IoResult, Write};

type LeafIndex = u8;
type SerialNumber<C> = <<C as Parameters>::AccountSignatureScheme as SignatureScheme>::PublicKey;
type Commitment<C> = <C as Parameters>::RecordCommitment;
type Memo<C> = <Transaction<C> as TransactionScheme>::Memorandum;
type NetworkId = u8;

#[derive(Derivative)]
#[derivative(
    Clone(bound = "C: Parameters"),
    Debug(bound = "C: Parameters"),
    PartialEq(bound = "C: Parameters"),
    Eq(bound = "C: Parameters")
)]
pub enum LocalDataLeaf<C: Parameters> {
    InputRecord(LeafIndex, SerialNumber<C>, Commitment<C>, Memo<C>, NetworkId),
    OutputRecord(LeafIndex, Commitment<C>, Memo<C>, NetworkId),
}

impl<C: Parameters> ToBytes for LocalDataLeaf<C> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        match self {
            Self::InputRecord(leaf_index, serial_number, commitment, memo, network_id) => {
                if (*leaf_index as usize) >= C::NUM_INPUT_RECORDS {
                    Err(DPCError::Message("Invalid local data input record leaf index".into()).into())
                } else {
                    to_bytes_le![leaf_index, serial_number, commitment, memo, network_id]?.write_le(&mut writer)
                }
            }
            Self::OutputRecord(leaf_index, commitment, memo, network_id) => {
                if (*leaf_index as usize) < C::NUM_INPUT_RECORDS || (*leaf_index as usize) >= C::NUM_OUTPUT_RECORDS {
                    return Err(DPCError::Message("Invalid local data output record leaf index".into()).into());
                } else {
                    to_bytes_le![leaf_index, commitment, memo, network_id]?.write_le(&mut writer)
                }
            }
        }
    }
}

impl<C: Parameters> FromBytes for LocalDataLeaf<C> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let index: u8 = FromBytes::read_le(&mut reader)?;

        // Use the leaf index to determine how to parse the reader.
        if (index as usize) < C::NUM_INPUT_RECORDS {
            let serial_number: SerialNumber<C> = FromBytes::read_le(&mut reader)?;
            let commitment: Commitment<C> = FromBytes::read_le(&mut reader)?;
            let memo: Memo<C> = FromBytes::read_le(&mut reader)?;
            let network_id: NetworkId = FromBytes::read_le(&mut reader)?;

            Ok(Self::InputRecord(index, serial_number, commitment, memo, network_id))
        } else if (index as usize) >= C::NUM_INPUT_RECORDS || (index as usize) < C::NUM_OUTPUT_RECORDS {
            let commitment: Commitment<C> = FromBytes::read_le(&mut reader)?;
            let memo: Memo<C> = FromBytes::read_le(&mut reader)?;
            let network_id: NetworkId = FromBytes::read_le(&mut reader)?;

            Ok(Self::OutputRecord(index, commitment, memo, network_id))
        } else {
            Err(DPCError::Message("Invalid local data leaf index".into()).into())
        }
    }
}
