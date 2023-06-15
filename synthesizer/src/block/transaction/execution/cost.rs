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

use super::*;

impl<N: Network> Execution<N> {
    /// Returns the *minimum* cost in microcredits to publish the given execution (total cost, (storage cost, namespace cost)).
    pub fn cost(execution: &Self, lookup: HashMap<ProgramID<N>, Program<N>>) -> Result<(u64, (u64, u64))> {
        // Compute the storage cost in microcredits.
        let storage_cost = execution.size_in_bytes()?;

        // Compute the finalize cost in microcredits.
        let mut finalize_cost = 0u64;
        // Iterate over the transitions to accumulate the finalize cost.
        for transition in execution.transitions() {
            // Retrieve the program ID.
            let program_id = transition.program_id();
            // Retrieve the function name.
            let function_name = transition.function_name();
            // Retrieve the program.
            let program = lookup.get(program_id).ok_or(anyhow!("Program '{program_id}' is missing"))?;
            // Retrieve the finalize cost.
            let cost = match program.get_function(function_name)?.finalize() {
                Some((_, finalize)) => finalize.cost_in_microcredits()?,
                None => continue,
            };
            // Accumulate the finalize cost.
            finalize_cost = finalize_cost
                .checked_add(cost)
                .ok_or(anyhow!("The finalize cost computation overflowed for an execution"))?;
        }

        // Compute the total cost in microcredits.
        let total_cost = storage_cost
            .checked_add(finalize_cost)
            .ok_or(anyhow!("The total cost computation overflowed for an execution"))?;

        Ok((total_cost, (storage_cost, finalize_cost)))
    }
}
