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

use crate::testnet1::Testnet1Components;
use snarkvm_algorithms::prelude::*;

use std::io::Result as IoResult;

#[derive(Derivative)]
#[derivative(Clone(bound = "C: Testnet1Components"))]
pub struct SystemParameters<C: Testnet1Components> {
    pub program_verification_key_commitment: C::ProgramIDCommitment,
    pub program_verification_key_crh: C::ProgramIDCRH,
}

impl<C: Testnet1Components> SystemParameters<C> {
    pub fn setup() -> Self {
        let time = start_timer!(|| "Program verifying key CRH setup");
        let program_verification_key_crh = C::ProgramIDCRH::setup("ProgramVerificationKeyCRH");
        end_timer!(time);

        let time = start_timer!(|| "Program verification key commitment setup");
        let program_verification_key_commitment = C::ProgramIDCommitment::setup("ProgramVerificationKeyCommitment");
        end_timer!(time);

        Self {
            program_verification_key_commitment,
            program_verification_key_crh,
        }
    }

    /// TODO (howardwu): TEMPORARY FOR PR #251.
    pub fn load() -> IoResult<Self> {
        Ok(Self::setup())
    }
}
