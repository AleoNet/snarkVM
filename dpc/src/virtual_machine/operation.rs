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
use snarkvm_algorithms::traits::*;
use snarkvm_fields::{ConstraintFieldError, ToConstraintField};
use snarkvm_utilities::{FromBytes, FromBytesDeserializer, ToBytes, ToBytesSerializer};

use anyhow::{anyhow, Result};
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};
use std::{
    collections::HashMap,
    fmt,
    io::{Read, Result as IoResult, Write},
    str::FromStr,
};

type Caller<N> = Address<N>;
type Recipient<N> = Address<N>;

#[derive(Derivative)]
#[derivative(
    Clone(bound = "N: Network"),
    Debug(bound = "N: Network"),
    PartialEq(bound = "N: Network"),
    Eq(bound = "N: Network")
)]
pub struct ProgramFunctions<N: Network>(pub HashMap<N::FunctionID, <N::ProgramSNARK as SNARK>::VerifyingKey>);

#[derive(Derivative)]
#[derivative(
    Clone(bound = "N: Network"),
    Debug(bound = "N: Network"),
    PartialEq(bound = "N: Network"),
    Eq(bound = "N: Network")
)]
pub enum Operation<N: Network> {
    /// Noop.
    Noop,
    /// Generates the given amount to the recipient address.
    Coinbase(Recipient<N>, AleoAmount),
    /// Transfers the given amount from the caller to the recipient address.
    Transfer(Caller<N>, Recipient<N>, AleoAmount),
    /// Invokes the given records on the function and inputs.
    Evaluate(N::FunctionID, FunctionType, FunctionInputs<N>),
    /// Deploys a program to the on-chain program registry.
    Deploy(Caller<N>, AleoAmount, N::ProgramID, ProgramFunctions<N>),
}

impl<N: Network> Operation<N> {
    /// Returns the operation ID.
    pub fn operation_id(&self) -> u16 {
        match self {
            Self::Noop => 0,
            Self::Coinbase(..) => 1,
            Self::Transfer(..) => 2,
            Self::Evaluate(..) => 3,
            Self::Deploy(..) => 4,
        }
    }

    pub fn function_id(&self) -> N::FunctionID {
        match self {
            Self::Noop | Self::Coinbase(..) | Self::Transfer(..) | Self::Deploy(..) => *N::noop_function_id(),
            Self::Evaluate(function_id, _, _) => *function_id,
        }
    }

    pub fn function_type(&self) -> FunctionType {
        match self {
            Self::Noop => FunctionType::Noop,
            Self::Coinbase(..) => FunctionType::Insert,
            Self::Transfer(..) => FunctionType::Full,
            Self::Evaluate(_, function_type, _) => *function_type,
            Self::Deploy(..) => FunctionType::Full,
        }
    }

    pub fn function_inputs(&self) -> Result<FunctionInputs<N>> {
        match self {
            Self::Evaluate(_, _, function_inputs) => Ok(function_inputs.clone()),
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

    pub fn is_deploy(&self) -> bool {
        matches!(self, Self::Deploy(..))
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
                let function_type = FromBytes::read_le(&mut reader)?;
                let function_inputs = FromBytes::read_le(&mut reader)?;
                Ok(Self::Evaluate(function_id, function_type, function_inputs))
            }
            4 => {
                let caller = FromBytes::read_le(&mut reader)?;
                let amount = FromBytes::read_le(&mut reader)?;
                let program_id = FromBytes::read_le(&mut reader)?;
                let functions = FromBytes::read_le(&mut reader)?;
                Ok(Self::Deploy(caller, amount, program_id, functions))
            }
            _ => unreachable!("Invalid operation during deserialization"),
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
            Self::Evaluate(function_id, function_type, function_inputs) => {
                function_id.write_le(&mut writer)?;
                function_type.write_le(&mut writer)?;
                function_inputs.write_le(&mut writer)
            }
            Self::Deploy(caller, amount, program_id, functions) => {
                caller.write_le(&mut writer)?;
                amount.write_le(&mut writer)?;
                program_id.write_le(&mut writer)?;
                functions.write_le(&mut writer)
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
                let function_type = serde_json::from_value(operation["function_type"].clone())?;
                let function_inputs = serde_json::from_value(operation["function_inputs"].clone())?;
                Ok(Self::Evaluate(function_id, function_type, function_inputs))
            }
            4 => {
                let caller = serde_json::from_value(operation["caller"].clone())?;
                let amount = serde_json::from_value(operation["amount"].clone())?;
                let program_id = serde_json::from_value(operation["program_id"].clone())?;
                let program_functions = serde_json::from_value(operation["functions"].clone())?;
                Ok(Self::Deploy(caller, amount, program_id, program_functions))
            }
            _ => unreachable!(format!("Invalid operation id {}", operation_id)),
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
            Self::Evaluate(function_id, function_type, function_inputs) => {
                serde_json::json!({
                    "id": self.operation_id(),
                    "function_id": function_id,
                    "function_type": function_type.id(),
                    "function_inputs": function_inputs
                })
            }
            Self::Deploy(caller, amount, program_id, functions) => {
                serde_json::json!({
                    "id": self.operation_id(),
                    "caller": caller,
                    "amount": amount,
                    "program_id": program_id,
                    "functions": functions
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

impl<N: Network> FromBytes for ProgramFunctions<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let mut result = HashMap::new();
        let num_functions: u32 = FromBytes::read_le(&mut reader)?;

        for _ in 0..num_functions {
            let function_id = FromBytes::read_le(&mut reader)?;
            let vk = FromBytes::read_le(&mut reader)?;
            result.insert(function_id, vk);
        }

        Ok(ProgramFunctions::<N>(result))
    }
}

impl<N: Network> ToBytes for ProgramFunctions<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        (self.0.len() as u32).write_le(&mut writer)?;
        for (function_id, vk) in self.0.iter() {
            function_id.write_le(&mut writer)?;
            vk.write_le(&mut writer)?;
        }
        Ok(())
    }
}

impl<N: Network> Serialize for ProgramFunctions<N> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => serializer.collect_str(self),
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for ProgramFunctions<N> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => FromStr::from_str(&String::deserialize(deserializer)?).map_err(de::Error::custom),
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "program_functions"),
        }
    }
}

impl<N: Network> FromStr for ProgramFunctions<N> {
    type Err = anyhow::Error;

    fn from_str(program_functions: &str) -> Result<Self, Self::Err> {
        let functions: HashMap<N::FunctionID, <N::ProgramSNARK as SNARK>::VerifyingKey> =
            serde_json::from_value(serde_json::Value::from_str(program_functions)?)?;

        Ok(Self(functions))
    }
}

impl<N: Network> fmt::Display for ProgramFunctions<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", serde_json::json!(self.0))
    }
}
