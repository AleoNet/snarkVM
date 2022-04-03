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

use crate::{Address, AleoAmount, FunctionInputs, Network};
use snarkvm_fields::{ConstraintFieldError, ToConstraintField};
use snarkvm_utilities::{error, FromBytes, FromBytesDeserializer, ToBytes, ToBytesSerializer};

use anyhow::{anyhow, Result};
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};
use std::{
    fmt,
    io::{Read, Result as IoResult, Write},
    str::FromStr,
};

type Caller<N> = Address<N>;
type Recipient<N> = Address<N>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Operation<N: Network> {
    /// Noop.
    Noop,
    /// Generates the given amount to the recipient address.
    Coinbase(Recipient<N>, AleoAmount),
    // TODO (raychu86): Refactor transfers to support multiple recipients.
    /// Transfers the given amount from the caller to the recipient address.
    Transfer(Caller<N>, Recipient<N>, AleoAmount),
    /// Invokes the given records on the function and inputs.
    Evaluate(N::FunctionID, FunctionInputs<N>),
}

impl<N: Network> Operation<N> {
    /// Returns the operation ID.
    pub fn operation_id(&self) -> u16 {
        match self {
            Self::Noop => 0,
            Self::Coinbase(..) => 1,
            Self::Transfer(..) => 2,
            Self::Evaluate(..) => 3,
        }
    }

    pub fn function_id(&self) -> Option<N::FunctionID> {
        match self {
            Self::Noop | Self::Coinbase(..) | Self::Transfer(..) => None,
            Self::Evaluate(function_id, _) => Some(*function_id),
        }
    }

    pub fn function_inputs(&self) -> Result<FunctionInputs<N>> {
        match self {
            Self::Evaluate(_, function_inputs) => Ok(function_inputs.clone()),
            _ => Err(anyhow!("operation does not have function inputs")),
        }
    }

    pub fn is_noop(&self) -> bool {
        matches!(self, Self::Noop)
    }

    pub fn is_coinbase(&self) -> bool {
        matches!(self, Self::Coinbase(..))
    }

    pub fn is_transfer(&self) -> bool {
        matches!(self, Self::Transfer(..))
    }

    pub fn is_evaluate(&self) -> bool {
        matches!(self, Self::Evaluate(..))
    }
}

impl<N: Network> FromBytes for Operation<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let operation_id: u16 = FromBytes::read_le(&mut reader)?;
        match operation_id {
            0 => Ok(Self::Noop),
            1 => {
                let recipient = FromBytes::read_le(&mut reader)?;
                let amount = FromBytes::read_le(&mut reader)?;
                Ok(Self::Coinbase(recipient, amount))
            }
            2 => {
                let caller = FromBytes::read_le(&mut reader)?;
                let recipient = FromBytes::read_le(&mut reader)?;
                let amount = FromBytes::read_le(&mut reader)?;
                Ok(Self::Transfer(caller, recipient, amount))
            }
            3 => {
                let function_id = FromBytes::read_le(&mut reader)?;
                let function_inputs = FromBytes::read_le(&mut reader)?;
                Ok(Self::Evaluate(function_id, function_inputs))
            }
            4.. => Err(error("Invalid operation ID during deserialization")),
        }
    }
}

impl<N: Network> ToBytes for Operation<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.operation_id().write_le(&mut writer)?;
        match self {
            Self::Noop => Ok(()),
            Self::Coinbase(recipient, amount) => {
                recipient.write_le(&mut writer)?;
                amount.write_le(&mut writer)
            }
            Self::Transfer(caller, recipient, amount) => {
                caller.write_le(&mut writer)?;
                recipient.write_le(&mut writer)?;
                amount.write_le(&mut writer)
            }
            Self::Evaluate(function_id, function_inputs) => {
                function_id.write_le(&mut writer)?;
                function_inputs.write_le(&mut writer)
            }
        }
    }
}

impl<N: Network> FromStr for Operation<N> {
    type Err = anyhow::Error;

    fn from_str(operation: &str) -> Result<Self, Self::Err> {
        let operation = serde_json::Value::from_str(operation)?;
        let operation_id: u8 = serde_json::from_value(operation["id"].clone())?;

        match operation_id {
            0 => Ok(Self::Noop),
            1 => {
                let recipient = serde_json::from_value(operation["recipient"].clone())?;
                let amount = serde_json::from_value(operation["amount"].clone())?;
                Ok(Self::Coinbase(recipient, amount))
            }
            2 => {
                let caller = serde_json::from_value(operation["caller"].clone())?;
                let recipient = serde_json::from_value(operation["recipient"].clone())?;
                let amount = serde_json::from_value(operation["amount"].clone())?;
                Ok(Self::Transfer(caller, recipient, amount))
            }
            3 => {
                let function_id = serde_json::from_value(operation["function_id"].clone())?;
                let function_inputs = serde_json::from_value(operation["function_inputs"].clone())?;
                Ok(Self::Evaluate(function_id, function_inputs))
            }
            4.. => Err(error("Invalid operation ID during deserialization").into()),
        }
    }
}

impl<N: Network> fmt::Display for Operation<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let operation = match self {
            Self::Noop => {
                serde_json::json!({
                    "id": self.operation_id(),
                })
            }
            Self::Coinbase(recipient, amount) => {
                serde_json::json!({
                    "id": self.operation_id(),
                    "recipient": recipient,
                    "amount": amount
                })
            }
            Self::Transfer(caller, recipient, amount) => {
                serde_json::json!({
                    "id": self.operation_id(),
                    "caller": caller,
                    "recipient": recipient,
                    "amount": amount
                })
            }
            Self::Evaluate(function_id, function_inputs) => {
                serde_json::json!({
                    "id": self.operation_id(),
                    "function_id": function_id,
                    "function_inputs": function_inputs
                })
            }
        };

        write!(f, "{}", operation)
    }
}

impl<N: Network> Serialize for Operation<N> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => serializer.collect_str(self),
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for Operation<N> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => FromStr::from_str(&String::deserialize(deserializer)?).map_err(de::Error::custom),
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "operation"),
        }
    }
}

impl<N: Network> ToConstraintField<N::InnerScalarField> for Operation<N> {
    fn to_field_elements(&self) -> Result<Vec<N::InnerScalarField>, ConstraintFieldError> {
        let v = ToConstraintField::<N::InnerScalarField>::to_field_elements(&[0u8][..])?;
        Ok(v)
    }
}
