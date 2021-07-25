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

use crate::{Parameters, ProgramError};
use snarkvm_parameters::{prelude::*, testnet2::*};
use snarkvm_utilities::FromBytes;

use rand::{CryptoRng, Rng};
use snarkvm_algorithms::SNARK;
use std::io::Result as IoResult;

#[derive(Derivative)]
#[derivative(Clone(bound = "C: Parameters"))]
pub struct ProgramSNARKUniversalSRS<C: Parameters>(pub <C::ProgramSNARK as SNARK>::UniversalSetupParameters);

impl<C: Parameters> ProgramSNARKUniversalSRS<C> {
    pub fn setup<R: Rng + CryptoRng>(
        config: &<C::ProgramSNARK as SNARK>::UniversalSetupConfig,
        rng: &mut R,
    ) -> Result<Self, ProgramError> {
        // TODO (raychu86): Handle this unwrap.
        Ok(Self(C::ProgramSNARK::universal_setup(config, rng).unwrap()))
    }
}

impl<C: Parameters> ProgramSNARKUniversalSRS<C> {
    pub fn load() -> IoResult<Self> {
        Ok(Self(From::from(FromBytes::read_le(
            UniversalSRSParameters::load_bytes()?.as_slice(),
        )?)))
    }
}
