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

use crate::prelude::*;
use snarkvm_utilities::{to_bytes_le, FromBytes, ToBytes};

use anyhow::Result;
use std::{
    fmt,
    io::{Read, Result as IoResult, Write},
    str::FromStr,
};

/// The transaction authorization contains caller signatures and is required to
/// produce the final transaction proof.
#[derive(Derivative)]
#[derivative(
    Clone(bound = "N: Network"),
    Debug(bound = "N: Network"),
    PartialEq(bound = "N: Network"),
    Eq(bound = "N: Network")
)]
pub struct TransactionAuthorization<N: Network> {
    pub kernel: TransactionKernel<N>,
    pub signatures: Vec<N::AccountSignature>,
}

impl<N: Network> TransactionAuthorization<N> {
    #[inline]
    pub fn from(transition: &StateTransition<N>, signatures: Vec<N::AccountSignature>) -> Self {
        debug_assert!(transition.kernel().is_valid());
        debug_assert_eq!(N::NUM_INPUT_RECORDS, signatures.len());

        Self {
            kernel: transition.kernel().clone(),
            signatures,
        }
    }

    #[inline]
    pub fn to_transaction_id(&self) -> Result<N::TransactionID> {
        self.kernel.to_transaction_id()
    }
}

impl<N: Network> ToBytes for TransactionAuthorization<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.kernel.write_le(&mut writer)?;
        self.signatures.write_le(&mut writer)?;
        Ok(())
    }
}

impl<N: Network> FromBytes for TransactionAuthorization<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let kernel: TransactionKernel<N> = FromBytes::read_le(&mut reader)?;

        let mut signatures = Vec::<N::AccountSignature>::with_capacity(N::NUM_INPUT_RECORDS);
        for _ in 0..N::NUM_INPUT_RECORDS {
            signatures.push(FromBytes::read_le(&mut reader)?);
        }

        Ok(Self { kernel, signatures })
    }
}

impl<N: Network> FromStr for TransactionAuthorization<N> {
    type Err = DPCError;

    fn from_str(kernel: &str) -> Result<Self, Self::Err> {
        Ok(Self::read_le(&hex::decode(kernel)?[..])?)
    }
}

impl<N: Network> fmt::Display for TransactionAuthorization<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            hex::encode(to_bytes_le![self].expect("couldn't serialize to bytes"))
        )
    }
}
