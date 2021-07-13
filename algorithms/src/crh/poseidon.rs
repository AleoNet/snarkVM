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

use crate::{
    crypto_hash::{PoseidonCryptoHash, PoseidonDefaultParametersField, PoseidonParameters},
    traits::{CryptoHash, CRH},
    CRHError,
    CRHParameters,
};

use snarkvm_fields::{PrimeField, ToConstraintField};
use snarkvm_utilities::{FromBytes, ToBytes};

use rand::Rng;
use std::{
    io::{Read, Result as IoResult, Write},
    marker::PhantomData,
};

// TODO (raychu86): Implement these trait functions.

impl<F: PrimeField + PoseidonDefaultParametersField> CRHParameters for PoseidonParameters<F> {
    fn setup<R: Rng>(_r: &mut R) -> Self {
        // TODO (raychu86): Don't use the hard coded rate and optimization flag.
        let params = F::get_default_poseidon_parameters(4, false).unwrap();

        params
    }
}

impl<F: PrimeField + PoseidonDefaultParametersField> ToBytes for PoseidonParameters<F> {
    #[inline]
    fn write_le<W: Write>(&self, mut _writer: W) -> IoResult<()> {
        unimplemented!()
    }
}

impl<F: PrimeField + PoseidonDefaultParametersField> FromBytes for PoseidonParameters<F> {
    #[inline]
    fn read_le<R: Read>(mut _reader: R) -> IoResult<Self> {
        unimplemented!()
    }
}

impl<F: PrimeField + PoseidonDefaultParametersField, const RATE: usize, const OPTIMIZED_FOR_WEIGHTS: bool> CRH
    for PoseidonCryptoHash<F, RATE, OPTIMIZED_FOR_WEIGHTS>
{
    type Output = F;
    type Parameters = PoseidonParameters<F>;

    // TODO (raychu86): Specify this value correctly. Currently an arbitrary value
    const INPUT_SIZE_BITS: usize = 48 * 48;

    fn setup<R: Rng>(_rng: &mut R) -> Self {
        Self {
            parameters: F::get_default_poseidon_parameters(RATE, OPTIMIZED_FOR_WEIGHTS).unwrap(),
        }
    }

    fn hash(&self, input: &[u8]) -> Result<Self::Output, CRHError> {
        Ok(Self::evaluate(&input.to_field_elements().unwrap())?)
    }

    fn parameters(&self) -> &Self::Parameters {
        &self.parameters
    }
}

impl<F: PrimeField + PoseidonDefaultParametersField, const RATE: usize, const OPTIMIZED_FOR_WEIGHTS: bool>
    From<PoseidonParameters<F>> for PoseidonCryptoHash<F, RATE, OPTIMIZED_FOR_WEIGHTS>
{
    fn from(parameters: PoseidonParameters<F>) -> Self {
        Self { parameters }
    }
}
