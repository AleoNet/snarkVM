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

use crate::{AleoAmount, Network, ValueBalanceCommitment};
use snarkvm_fields::{ConstraintFieldError, ToConstraintField};
use snarkvm_utilities::ToBytes;

use anyhow::Result;

#[derive(Clone, Debug)]
pub struct ValueCheckPublicVariables<N: Network> {
    /// A value balance is the difference between the input and output record values.
    value_balance: AleoAmount,
    /// The value balance commitments.
    value_balance_commitment: N::ValueBalanceCommitment,
}

impl<N: Network> ValueCheckPublicVariables<N> {
    pub(crate) fn blank() -> Self {
        Self { value_balance: AleoAmount::ZERO, value_balance_commitment: ValueBalanceCommitment::default().into() }
    }

    pub(crate) fn new(value_balance: AleoAmount, value_balance_commitment: N::ValueBalanceCommitment) -> Self {
        Self { value_balance, value_balance_commitment }
    }

    /// Returns the value balance of the transition.
    pub(crate) fn value_balance(&self) -> AleoAmount {
        self.value_balance
    }

    /// Returns the value balance commitment.
    pub(crate) fn value_balance_commitment(&self) -> &N::ValueBalanceCommitment {
        &self.value_balance_commitment
    }
}

impl<N: Network> ToConstraintField<N::InnerScalarField> for ValueCheckPublicVariables<N> {
    fn to_field_elements(&self) -> Result<Vec<N::InnerScalarField>, ConstraintFieldError> {
        let mut v = Vec::new();

        v.extend_from_slice(&self.value_balance.to_bytes_le()?.to_field_elements()?);
        v.extend_from_slice(&self.value_balance_commitment().to_field_elements()?);

        Ok(v)
    }
}
