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

use crate::{virtual_machine::AleoAmount, Address, Network, Payload};
use snarkvm_algorithms::CRH;
use snarkvm_fields::{ConstraintFieldError, ToConstraintField};
use snarkvm_utilities::{FromBytes, ToBytes};

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::io::{Read, Result as IoResult, Write};

type Caller<N> = Address<N>;
type Recipient<N> = Address<N>;

#[derive(Derivative, Serialize, Deserialize)]
#[derivative(
    Clone(bound = "N: Network"),
    Debug(bound = "N: Network"),
    PartialEq(bound = "N: Network")
)]
pub struct FunctionInputs<N: Network> {
    #[serde(skip)]
    pub(crate) caller: Caller<N>,
    #[serde(skip)]
    pub(crate) recipient: Recipient<N>,
    pub(crate) amount: AleoAmount,
    pub(crate) record_payload: Payload<N>,
}

impl<N: Network> FunctionInputs<N> {
    pub fn new(caller: &Caller<N>, recipient: &Recipient<N>, amount: AleoAmount, record_payload: Payload<N>) -> Self {
        Self {
            caller: *caller,
            recipient: *recipient,
            amount,
            record_payload,
        }
    }

    /// Returns a hash of the function inputs.
    pub fn to_hash(&self) -> Result<N::FunctionInputsHash> {
        Ok(N::FunctionInputsCRH::setup("UnusedInPoseidon")
            .hash_field_elements(&self.to_field_elements()?)?
            .into())
    }
}

impl<N: Network> FromBytes for FunctionInputs<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let caller = FromBytes::read_le(&mut reader)?;
        let recipient = FromBytes::read_le(&mut reader)?;
        let amount = FromBytes::read_le(&mut reader)?;
        let record_payload = FromBytes::read_le(&mut reader)?;

        Ok(Self {
            caller,
            recipient,
            amount,
            record_payload,
        })
    }
}

impl<N: Network> ToBytes for FunctionInputs<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.caller.write_le(&mut writer)?;
        self.recipient.write_le(&mut writer)?;
        self.amount.write_le(&mut writer)?;
        self.record_payload.write_le(&mut writer)
    }
}

impl<N: Network> ToConstraintField<N::InnerScalarField> for FunctionInputs<N> {
    fn to_field_elements(&self) -> Result<Vec<N::InnerScalarField>, ConstraintFieldError> {
        // let v = ToConstraintField::<N::InnerScalarField>::to_field_elements(&[0u8][..])?;
        // Ok(v)

        unimplemented!()
    }
}
