// Copyright (C) 2019-2022 Aleo Systems Inc.
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

use crate::{Address, AleoAmount, Network, Payload};
use snarkvm_fields::{ConstraintFieldError, ToConstraintField};
use snarkvm_utilities::{FromBytes, FromBytesDeserializer, ToBytes, ToBytesSerializer};

use anyhow::Result;
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};
use std::{
    fmt,
    io::{Read, Result as IoResult, Write},
    str::FromStr,
};

type Caller<N> = Address<N>;
type Recipient<N> = Address<N>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionInputs<N: Network> {
    pub(crate) caller: Caller<N>,
    pub(crate) recipient: Recipient<N>,
    pub(crate) amount: AleoAmount,
    pub(crate) record_payload: Payload<N>,
}

impl<N: Network> FunctionInputs<N> {
    pub fn new(caller: &Caller<N>, recipient: &Recipient<N>, amount: AleoAmount, record_payload: Payload<N>) -> Self {
        Self { caller: *caller, recipient: *recipient, amount, record_payload }
    }
}

impl<N: Network> FromBytes for FunctionInputs<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let caller = FromBytes::read_le(&mut reader)?;
        let recipient = FromBytes::read_le(&mut reader)?;
        let amount = FromBytes::read_le(&mut reader)?;
        let record_payload = FromBytes::read_le(&mut reader)?;

        Ok(Self { caller, recipient, amount, record_payload })
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

impl<N: Network> FromStr for FunctionInputs<N> {
    type Err = anyhow::Error;

    fn from_str(function_inputs: &str) -> Result<Self, Self::Err> {
        let function_inputs = serde_json::Value::from_str(function_inputs)?;

        // Recover the function inputs.
        Ok(Self::new(
            &serde_json::from_value(function_inputs["caller"].clone())?,
            &serde_json::from_value(function_inputs["recipient"].clone())?,
            serde_json::from_value(function_inputs["amount"].clone())?,
            serde_json::from_value(function_inputs["record_payload"].clone())?,
        ))
    }
}

impl<N: Network> fmt::Display for FunctionInputs<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let function_inputs = serde_json::json!({
            "caller": self.caller,
            "recipient": self.recipient,
            "amount": self.amount,
            "record_payload": self.record_payload,
        });

        write!(f, "{}", function_inputs)
    }
}

impl<N: Network> Serialize for FunctionInputs<N> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => serializer.collect_str(self),
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for FunctionInputs<N> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => FromStr::from_str(&String::deserialize(deserializer)?).map_err(de::Error::custom),
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "function_inputs"),
        }
    }
}

impl<N: Network> ToConstraintField<N::InnerScalarField> for FunctionInputs<N> {
    fn to_field_elements(&self) -> Result<Vec<N::InnerScalarField>, ConstraintFieldError> {
        // let v = ToConstraintField::<N::InnerScalarField>::to_field_elements(&[0u8][..])?;
        // Ok(v)

        unimplemented!()
    }
}
