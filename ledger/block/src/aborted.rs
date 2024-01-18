// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use thiserror::Error;

/// The error type for Aborted Transactions.
#[derive(Clone, Copy, Debug, Error, PartialEq, Eq)]
#[repr(u8)]
pub enum AbortedError {
    #[error("Exceeds block transaction limit.")]
    ExceedsTransactionLimit = 0,

    #[error("Double-spending input.")]
    DoubleSpendInput = 1,

    #[error("Duplicate output.")]
    DuplicateOutput = 2,

    #[error("Fee finalization failed for an existing deployment.")]
    FeeFinalizeFailedForExistingDeployment = 3,

    #[error("Fee finalization failed for a new deployment.")]
    FeeFinalizeFailedForNewDeployment = 4,

    #[error("Fee finalization failed for a new execution.")]
    FeeFinalizeFailedForNewExecution = 5,
}

impl TryFrom<u8> for AbortedError {
    type Error = String;

    fn try_from(v: u8) -> Result<Self, Self::Error> {
        match v {
            x if x == AbortedError::ExceedsTransactionLimit as u8 => Ok(AbortedError::ExceedsTransactionLimit),
            x if x == AbortedError::DoubleSpendInput as u8 => Ok(AbortedError::DoubleSpendInput),
            x if x == AbortedError::DuplicateOutput as u8 => Ok(AbortedError::DuplicateOutput),
            x if x == AbortedError::FeeFinalizeFailedForExistingDeployment as u8 => {
                Ok(AbortedError::FeeFinalizeFailedForExistingDeployment)
            }
            x if x == AbortedError::FeeFinalizeFailedForNewDeployment as u8 => {
                Ok(AbortedError::FeeFinalizeFailedForNewDeployment)
            }
            x if x == AbortedError::FeeFinalizeFailedForNewExecution as u8 => {
                Ok(AbortedError::FeeFinalizeFailedForNewExecution)
            }
            _ => Err("Could not convert u8 to AbortedError.".to_string()),
        }
    }
}
