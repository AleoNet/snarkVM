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

use crate::{Address, AleoAmount, FunctionInputs, FunctionType, Network};
use snarkvm_algorithms::prelude::*;
use snarkvm_fields::{ConstraintFieldError, ToConstraintField};
use snarkvm_utilities::{FromBytes, ToBytes};

use anyhow::Result;
use std::io::{Read, Result as IoResult, Write};

#[derive(Derivative)]
#[derivative(Clone(bound = "N: Network"), Debug(bound = "N: Network"))]
pub enum Operation<N: Network> {
    /// Noop.
    Noop,
    /// Generates the given amount to the recipient address.
    Coinbase(Address<N>, AleoAmount),
    /// Transfers the given amount to the recipient address.
    Transfer(Address<N>, AleoAmount),
    /// Invokes the given records on the function and inputs.
    Execute(N::FunctionID, FunctionType, FunctionInputs<N>),
}

impl<N: Network> Operation<N> {
    pub fn function_id(&self) -> N::FunctionID {
        match self {
            Self::Noop | Self::Coinbase(..) | Self::Transfer(..) => *N::noop_function_id(),
            Self::Execute(function_id, _, _) => *function_id,
        }
    }

    pub fn function_type(&self) -> FunctionType {
        match self {
            Self::Noop => FunctionType::Noop,
            Self::Coinbase(..) => FunctionType::Add,
            Self::Transfer(..) => FunctionType::Full,
            Self::Execute(_, function_type, _) => *function_type,
        }
    }

    /// Returns a hash of the operation.
    pub fn to_operation_id(&self) -> Result<N::FunctionInputsDigest> {
        Ok(N::FunctionInputsCRH::setup("UnusedInPoseidon").hash_field_elements(&self.to_field_elements()?)?)
    }
}

impl<N: Network> FromBytes for Operation<N> {
    #[inline]
    fn read_le<R: Read>(_reader: R) -> IoResult<Self> {
        Ok(Self::Noop)
    }
}

impl<N: Network> ToBytes for Operation<N> {
    #[inline]
    fn write_le<W: Write>(&self, _writer: W) -> IoResult<()> {
        Ok(())
    }
}

impl<N: Network> ToConstraintField<N::InnerScalarField> for Operation<N> {
    fn to_field_elements(&self) -> Result<Vec<N::InnerScalarField>, ConstraintFieldError> {
        let v = ToConstraintField::<N::InnerScalarField>::to_field_elements(&[0u8][..])?;
        Ok(v)
    }
}
