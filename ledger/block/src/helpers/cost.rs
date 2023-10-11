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

use crate::{Deployment, Execution};
use console::prelude::*;

/// Returns storage cost of the deployment in microcredits.
pub fn deployment_storage_cost<N: Network>(deployment: &Deployment<N>) -> Result<u64> {
    // Determine the number of bytes in the deployment.
    let size_in_bytes = deployment.size_in_bytes()?;

    // Compute the storage cost in microcredits.
    let storage_cost = size_in_bytes
        .checked_mul(N::DEPLOYMENT_FEE_MULTIPLIER)
        .ok_or(anyhow!("The storage cost computation overflowed for a deployment"))?;

    Ok(storage_cost)
}

/// Returns namespace cost of the deployment in microcredits.
pub fn deployment_namespace_cost<N: Network>(deployment: &Deployment<N>) -> Result<u64> {
    // Retrieve the program ID.
    let program_id = deployment.program_id();
    // Determine the number of characters in the program ID.
    let num_characters = u32::try_from(program_id.name().to_string().len())?;
    // Compute the namespace cost in credits: 10^(10 - num_characters).
    let namespace_cost = 10u64
        .checked_pow(10u32.saturating_sub(num_characters))
        .ok_or(anyhow!("The namespace cost computation overflowed for a deployment"))?
        .saturating_mul(1_000_000); // 1 microcredit = 1e-6 credits.

    Ok(namespace_cost)
}

/// Returns the storage cost of the execution in microcredits.
pub fn execution_storage_cost<N: Network>(execution: &Execution<N>) -> Result<u64> {
    execution.size_in_bytes()
}
