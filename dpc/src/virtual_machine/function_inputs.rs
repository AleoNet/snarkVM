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
use snarkvm_algorithms::CRH;
use snarkvm_fields::{ConstraintFieldError, ToConstraintField};
use snarkvm_utilities::{FromBytes, ToBytes};

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::{
    io::{Read, Result as IoResult, Write},
    marker::PhantomData,
};

#[derive(Derivative, Serialize, Deserialize)]
#[derivative(
    Copy(bound = "N: Network"),
    Clone(bound = "N: Network"),
    Debug(bound = "N: Network"),
    Default(bound = "N: Network"),
    PartialEq(bound = "N: Network")
)]
pub struct FunctionInputs<N: Network> {
    #[serde(skip)]
    _unused: PhantomData<N>,
}

impl<N: Network> FunctionInputs<N> {
    pub fn new() -> Self {
        Self { _unused: PhantomData }
    }

    /// Returns a hash of the function inputs.
    pub fn to_hash(&self) -> Result<N::FunctionInputsDigest> {
        Ok(N::FunctionInputsCRH::setup("UnusedInPoseidon").hash_field_elements(&self.to_field_elements()?)?)
    }
}

impl<N: Network> FromBytes for FunctionInputs<N> {
    #[inline]
    fn read_le<R: Read>(_reader: R) -> IoResult<Self> {
        Ok(Self::new())
    }
}

impl<N: Network> ToBytes for FunctionInputs<N> {
    #[inline]
    fn write_le<W: Write>(&self, _writer: W) -> IoResult<()> {
        Ok(())
    }
}

impl<N: Network> ToConstraintField<N::InnerScalarField> for FunctionInputs<N> {
    fn to_field_elements(&self) -> Result<Vec<N::InnerScalarField>, ConstraintFieldError> {
        let v = ToConstraintField::<N::InnerScalarField>::to_field_elements(&[0u8][..])?;
        Ok(v)
    }
}
