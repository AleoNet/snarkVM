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

use crate::Network;
use snarkvm_algorithms::merkle_tree::MerklePath;
use snarkvm_utilities::{FromBytes, ToBytes};

use std::io::{Read, Result as IoResult, Write};

/// Program ID, program path, verifying key, and proof.
#[derive(Derivative)]
#[derivative(Clone(bound = "N: Network"), Debug(bound = "N: Network"))]
pub struct Execution<N: Network> {
    pub program_id: N::ProgramID,
    pub program_path: MerklePath<N::ProgramIDParameters>,
    #[derivative(Debug = "ignore")]
    pub verifying_key: N::ProgramVerifyingKey,
    pub proof: N::ProgramProof,
}

impl<N: Network> FromBytes for Execution<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let program_id = FromBytes::read_le(&mut reader)?;
        let program_path = FromBytes::read_le(&mut reader)?;
        let verifying_key = FromBytes::read_le(&mut reader)?;
        let proof = FromBytes::read_le(&mut reader)?;

        Ok(Self {
            program_id,
            program_path,
            verifying_key,
            proof,
        })
    }
}

impl<N: Network> ToBytes for Execution<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.program_id.write_le(&mut writer)?;
        self.program_path.write_le(&mut writer)?;
        self.verifying_key.write_le(&mut writer)?;
        self.proof.write_le(&mut writer)
    }
}
