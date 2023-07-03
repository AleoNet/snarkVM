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

use crate::VM;
use console::{prelude::*, program::LiteralType};
use ledger_block::{Deployment, Execution};
use ledger_store::ConsensusStorage;
use synthesizer_program::{Command, Finalize, Instruction};

use std::collections::HashMap;

/// Returns the *minimum* cost in microcredits to publish the given deployment (total cost, (storage cost, namespace cost)).
pub fn deployment_cost<N: Network>(deployment: &Deployment<N>) -> Result<(u64, (u64, u64))> {
    // Determine the number of bytes in the deployment.
    let size_in_bytes = deployment.size_in_bytes()?;
    // Retrieve the program ID.
    let program_id = deployment.program_id();
    // Determine the number of characters in the program ID.
    let num_characters = u32::try_from(program_id.name().to_string().len())?;

    // Compute the storage cost in microcredits.
    let storage_cost = size_in_bytes
        .checked_mul(N::DEPLOYMENT_FEE_MULTIPLIER)
        .ok_or(anyhow!("The storage cost computation overflowed for a deployment"))?;

    // Compute the namespace cost in credits: 10^(10 - num_characters).
    let namespace_cost = 10u64
        .checked_pow(10u32.saturating_sub(num_characters))
        .ok_or(anyhow!("The namespace cost computation overflowed for a deployment"))?
        .saturating_mul(1_000_000); // 1 microcredit = 1e-6 credits.

    // Compute the total cost in microcredits.
    let total_cost = storage_cost
        .checked_add(namespace_cost)
        .ok_or(anyhow!("The total cost computation overflowed for a deployment"))?;

    Ok((total_cost, (storage_cost, namespace_cost)))
}

/// Returns the *minimum* cost in microcredits to publish the given execution (total cost, (storage cost, namespace cost)).
pub fn execution_cost<N: Network, C: ConsensusStorage<N>>(
    vm: &VM<N, C>,
    execution: &Execution<N>,
) -> Result<(u64, (u64, u64))> {
    // Compute the storage cost in microcredits.
    let storage_cost = execution.size_in_bytes()?;

    // Prepare the program lookup.
    let lookup = execution
        .transitions()
        .map(|transition| {
            let program_id = transition.program_id();
            Ok((*program_id, vm.process().read().get_program(program_id)?.clone()))
        })
        .collect::<Result<HashMap<_, _>>>()?;

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
            Some((_, finalize)) => cost_in_microcredits(finalize)?,
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

/// Returns the minimum number of microcredits required to run the finalize.
pub fn cost_in_microcredits<N: Network>(finalize: &Finalize<N>) -> Result<u64> {
    // Defines the cost of each command.
    let cost = |command: &Command<N>| match command {
        Command::Instruction(Instruction::Abs(_)) => Ok(2_000),
        Command::Instruction(Instruction::AbsWrapped(_)) => Ok(2_000),
        Command::Instruction(Instruction::Add(_)) => Ok(2_000),
        Command::Instruction(Instruction::AddWrapped(_)) => Ok(2_000),
        Command::Instruction(Instruction::And(_)) => Ok(2_000),
        Command::Instruction(Instruction::AssertEq(_)) => Ok(2_000),
        Command::Instruction(Instruction::AssertNeq(_)) => Ok(2_000),
        Command::Instruction(Instruction::Call(_)) => bail!("`call` is not supported in finalize."),
        Command::Instruction(Instruction::Cast(_)) => Ok(2_000),
        Command::Instruction(Instruction::CommitBHP256(_)) => Ok(200_000),
        Command::Instruction(Instruction::CommitBHP512(_)) => Ok(200_000),
        Command::Instruction(Instruction::CommitBHP768(_)) => Ok(200_000),
        Command::Instruction(Instruction::CommitBHP1024(_)) => Ok(200_000),
        Command::Instruction(Instruction::CommitPED64(_)) => Ok(100_000),
        Command::Instruction(Instruction::CommitPED128(_)) => Ok(100_000),
        Command::Instruction(Instruction::Div(_)) => Ok(10_000),
        Command::Instruction(Instruction::DivWrapped(_)) => Ok(2_000),
        Command::Instruction(Instruction::Double(_)) => Ok(2_000),
        Command::Instruction(Instruction::GreaterThan(_)) => Ok(2_000),
        Command::Instruction(Instruction::GreaterThanOrEqual(_)) => Ok(2_000),
        Command::Instruction(Instruction::HashBHP256(_)) => Ok(200_000),
        Command::Instruction(Instruction::HashBHP512(_)) => Ok(100_000),
        Command::Instruction(Instruction::HashBHP768(_)) => Ok(100_000),
        Command::Instruction(Instruction::HashBHP1024(_)) => Ok(100_000),
        Command::Instruction(Instruction::HashPED64(_)) => Ok(20_000),
        Command::Instruction(Instruction::HashPED128(_)) => Ok(30_000),
        Command::Instruction(Instruction::HashPSD2(hash)) => match hash.destination_type() {
            LiteralType::Address | LiteralType::Group => Ok(600_000),
            _ => Ok(60_000),
        },
        Command::Instruction(Instruction::HashPSD4(hash)) => match hash.destination_type() {
            LiteralType::Address | LiteralType::Group => Ok(700_000),
            _ => Ok(100_000),
        },
        Command::Instruction(Instruction::HashPSD8(hash)) => match hash.destination_type() {
            LiteralType::Address | LiteralType::Group => Ok(800_000),
            _ => Ok(200_000),
        },
        Command::Instruction(Instruction::HashManyPSD2(_)) => {
            bail!("`hash_many.psd2` is not supported in finalize.")
        }
        Command::Instruction(Instruction::HashManyPSD4(_)) => {
            bail!("`hash_many.psd4` is not supported in finalize.")
        }
        Command::Instruction(Instruction::HashManyPSD8(_)) => {
            bail!("`hash_many.psd8` is not supported in finalize.")
        }
        Command::Instruction(Instruction::Inv(_)) => Ok(10_000),
        Command::Instruction(Instruction::IsEq(_)) => Ok(2_000),
        Command::Instruction(Instruction::IsNeq(_)) => Ok(2_000),
        Command::Instruction(Instruction::LessThan(_)) => Ok(2_000),
        Command::Instruction(Instruction::LessThanOrEqual(_)) => Ok(2_000),
        Command::Instruction(Instruction::Modulo(_)) => Ok(2_000),
        Command::Instruction(Instruction::Mul(_)) => Ok(150_000),
        Command::Instruction(Instruction::MulWrapped(_)) => Ok(2_000),
        Command::Instruction(Instruction::Nand(_)) => Ok(2_000),
        Command::Instruction(Instruction::Neg(_)) => Ok(2_000),
        Command::Instruction(Instruction::Nor(_)) => Ok(2_000),
        Command::Instruction(Instruction::Not(_)) => Ok(2_000),
        Command::Instruction(Instruction::Or(_)) => Ok(2_000),
        Command::Instruction(Instruction::Pow(_)) => Ok(20_000),
        Command::Instruction(Instruction::PowWrapped(_)) => Ok(2_000),
        Command::Instruction(Instruction::Rem(_)) => Ok(2_000),
        Command::Instruction(Instruction::RemWrapped(_)) => Ok(2_000),
        Command::Instruction(Instruction::Shl(_)) => Ok(2_000),
        Command::Instruction(Instruction::ShlWrapped(_)) => Ok(2_000),
        Command::Instruction(Instruction::Shr(_)) => Ok(2_000),
        Command::Instruction(Instruction::ShrWrapped(_)) => Ok(2_000),
        Command::Instruction(Instruction::Square(_)) => Ok(2_000),
        Command::Instruction(Instruction::SquareRoot(_)) => Ok(120_000),
        Command::Instruction(Instruction::Sub(_)) => Ok(10_000),
        Command::Instruction(Instruction::SubWrapped(_)) => Ok(2_000),
        Command::Instruction(Instruction::Ternary(_)) => Ok(2_000),
        Command::Instruction(Instruction::Xor(_)) => Ok(2_000),
        // TODO: The following 'finalize' commands are currently priced higher than expected.
        //  Expect these numbers to change as their usage is stabilized.
        Command::Contains(_) => Ok(250_000),
        Command::Get(_) => Ok(500_000),
        Command::GetOrUse(_) => Ok(500_000),
        Command::RandChaCha(_) => Ok(500_000),
        Command::Remove(_) => Ok(10_000),
        Command::Set(_) => Ok(1_000_000),
        Command::BranchEq(_) | Command::BranchNeq(_) => Ok(5_000),
        Command::Position(_) => Ok(1_000),
    };
    finalize.commands().iter().map(|command| cost(command)).sum()
}
