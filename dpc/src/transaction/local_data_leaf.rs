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

use crate::{DPCError, Memo, Network};
use snarkvm_utilities::{to_bytes_le, FromBytes, ToBytes};

use std::io::{Read, Result as IoResult, Write};

type LeafIndex = u8;
type SerialNumber<N> = <N as Network>::SerialNumber;
type Commitment<N> = <N as Network>::RecordCommitment;
type NetworkId = u16;

#[derive(Derivative)]
#[derivative(
    Clone(bound = "N: Network"),
    Debug(bound = "N: Network"),
    PartialEq(bound = "N: Network"),
    Eq(bound = "N: Network")
)]
pub enum LocalDataLeaf<N: Network> {
    InputRecord(LeafIndex, SerialNumber<N>, Commitment<N>, Memo<N>, NetworkId),
    OutputRecord(LeafIndex, Commitment<N>, Memo<N>, NetworkId),
}

impl<N: Network> ToBytes for LocalDataLeaf<N> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        match self {
            Self::InputRecord(leaf_index, serial_number, commitment, memo, network_id) => {
                if (*leaf_index as usize) >= N::NUM_INPUT_RECORDS {
                    return Err(DPCError::Message(format!("Invalid local data input index - {}", leaf_index)).into());
                } else {
                    to_bytes_le![leaf_index, serial_number, commitment, memo, network_id]?.write_le(&mut writer)
                }
            }
            Self::OutputRecord(leaf_index, commitment, memo, network_id) => {
                if (*leaf_index as usize) < N::NUM_INPUT_RECORDS || (*leaf_index as usize) >= N::NUM_TOTAL_RECORDS {
                    return Err(DPCError::Message(format!("Invalid local data output index - {}", leaf_index)).into());
                } else {
                    to_bytes_le![leaf_index, commitment, memo, network_id]?.write_le(&mut writer)
                }
            }
        }
    }
}

impl<N: Network> FromBytes for LocalDataLeaf<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let index: u8 = FromBytes::read_le(&mut reader)?;

        // Use the leaf index to determine how to parse the reader.
        if (index as usize) < N::NUM_INPUT_RECORDS {
            let serial_number: SerialNumber<N> = FromBytes::read_le(&mut reader)?;
            let commitment: Commitment<N> = FromBytes::read_le(&mut reader)?;
            let memo: Memo<N> = FromBytes::read_le(&mut reader)?;
            let network_id: NetworkId = FromBytes::read_le(&mut reader)?;

            Ok(Self::InputRecord(index, serial_number, commitment, memo, network_id))
        } else if (index as usize) >= N::NUM_INPUT_RECORDS && (index as usize) < N::NUM_TOTAL_RECORDS {
            let commitment: Commitment<N> = FromBytes::read_le(&mut reader)?;
            let memo: Memo<N> = FromBytes::read_le(&mut reader)?;
            let network_id: NetworkId = FromBytes::read_le(&mut reader)?;

            Ok(Self::OutputRecord(index, commitment, memo, network_id))
        } else {
            Err(DPCError::Message(format!("Invalid local data leaf index - {}", index)).into())
        }
    }
}
