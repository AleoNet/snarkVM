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

    pub fn function_id(&self) -> N::FunctionID {
        match self {
            Self::Noop | Self::Coinbase(..) | Self::Transfer(..) => *N::noop_function_id(),
            Self::Evaluate(function_id, _, _) => *function_id,
        }
    }

    pub fn function_type(&self) -> FunctionType {
        match self {
            Self::Noop => FunctionType::Noop,
            Self::Coinbase(..) => FunctionType::Insert,
            Self::Transfer(..) => FunctionType::Full,
            Self::Evaluate(_, function_type, _) => *function_type,
        }
    }

    pub fn is_coinbase(&self) -> bool {
        match self {
            Self::Coinbase(..) => true,
            _ => false,
        }
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
            Self::Evaluate(function_id, _, _) => function_id.write_le(&mut writer),
        }
    }
}

impl<N: Network> ToConstraintField<N::InnerScalarField> for Operation<N> {
    fn to_field_elements(&self) -> Result<Vec<N::InnerScalarField>, ConstraintFieldError> {
        let v = ToConstraintField::<N::InnerScalarField>::to_field_elements(&[0u8][..])?;
        Ok(v)
    }
}
