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

use crate::{Process, Stack, StackProgramTypes};

use console::{
    prelude::*,
    program::{FinalizeType, Identifier, LiteralType, PlaintextType},
};
use ledger_block::{Deployment, Execution};
use synthesizer_program::{CastType, Command, Finalize, Instruction, Operand, StackProgram};

/// Returns the *minimum* cost in microcredits to publish the given deployment (total cost, (storage cost, synthesis cost, namespace cost)).
pub fn deployment_cost<N: Network>(deployment: &Deployment<N>) -> Result<(u64, (u64, u64, u64))> {
    // Determine the number of bytes in the deployment.
    let size_in_bytes = deployment.size_in_bytes()?;
    // Retrieve the program ID.
    let program_id = deployment.program_id();
    // Determine the number of characters in the program ID.
    let num_characters = u32::try_from(program_id.name().to_string().len())?;
    // Compute the number of combined variables in the program.
    let num_combined_variables = deployment.num_combined_variables()?;
    // Compute the number of combined constraints in the program.
    let num_combined_constraints = deployment.num_combined_constraints()?;

    // Compute the storage cost in microcredits.
    let storage_cost = size_in_bytes
        .checked_mul(N::DEPLOYMENT_FEE_MULTIPLIER)
        .ok_or(anyhow!("The storage cost computation overflowed for a deployment"))?;

    // Compute the synthesis cost in microcredits.
    let synthesis_cost = num_combined_variables.saturating_add(num_combined_constraints) * N::SYNTHESIS_FEE_MULTIPLIER;

    // Compute the namespace cost in credits: 10^(10 - num_characters).
    let namespace_cost = 10u64
        .checked_pow(10u32.saturating_sub(num_characters))
        .ok_or(anyhow!("The namespace cost computation overflowed for a deployment"))?
        .saturating_mul(1_000_000); // 1 microcredit = 1e-6 credits.

    // Compute the total cost in microcredits.
    let total_cost = storage_cost
        .checked_add(synthesis_cost)
        .and_then(|x| x.checked_add(namespace_cost))
        .ok_or(anyhow!("The total cost computation overflowed for a deployment"))?;

    Ok((total_cost, (storage_cost, synthesis_cost, namespace_cost)))
}

/// Returns the *minimum* cost in microcredits to publish the given execution (total cost, (storage cost, finalize cost)).
pub fn execution_cost<N: Network>(process: &Process<N>, execution: &Execution<N>) -> Result<(u64, (u64, u64))> {
    // Compute the storage cost in microcredits.
    let mut storage_cost = execution.size_in_bytes()?;

    // Compute a storage cost penalty if above the size penalty threshold.
    if storage_cost > N::EXECUTION_STORAGE_PENALTY_THRESHOLD {
        storage_cost = storage_cost.saturating_mul(N::EXECUTION_STORAGE_FEE_MULTIPLIER)
    }

    // Get the root transition.
    let transition = execution.peek()?;

    // Get the finalize cost for the root transition.
    let finalize_cost = process.get_stack(transition.program_id())?.get_finalize_cost(transition.function_name())?;

    // Compute the total cost in microcredits.
    let total_cost = storage_cost
        .checked_add(finalize_cost)
        .ok_or(anyhow!("The total cost computation overflowed for an execution"))?;

    Ok((total_cost, (storage_cost, finalize_cost)))
}

/// Finalize costs for compute heavy operations, derived as:
/// `BASE_COST + (PER_BYTE_COST * SIZE_IN_BYTES)`.

const CAST_BASE_COST: u64 = 500;
const CAST_PER_BYTE_COST: u64 = 30;

const HASH_BASE_COST: u64 = 10_000;
const HASH_PER_BYTE_COST: u64 = 30;

const HASH_BHP_BASE_COST: u64 = 50_000;
const HASH_BHP_PER_BYTE_COST: u64 = 300;

const HASH_PSD_BASE_COST: u64 = 40_000;
const HASH_PSD_PER_BYTE_COST: u64 = 75;

const MAPPING_BASE_COST: u64 = 10_000;
const MAPPING_PER_BYTE_COST: u64 = 10;

const SET_BASE_COST: u64 = 10_000;
const SET_PER_BYTE_COST: u64 = 100;

/// A helper function to determine the plaintext type in bytes.
fn plaintext_size_in_bytes<N: Network>(stack: &Stack<N>, plaintext_type: &PlaintextType<N>) -> Result<u64> {
    match plaintext_type {
        PlaintextType::Literal(literal_type) => Ok(literal_type.size_in_bytes::<N>() as u64),
        PlaintextType::Struct(struct_name) => {
            // Retrieve the struct from the stack.
            let struct_ = stack.program().get_struct(struct_name)?;
            // Retrieve the size of the struct name.
            let size_of_name = struct_.name().to_bytes_le()?.len() as u64;
            // Retrieve the size of all the members of the struct.
            let size_of_members = struct_.members().iter().try_fold(0u64, |acc, (_, member_type)| {
                acc.checked_add(plaintext_size_in_bytes(stack, member_type)?).ok_or(anyhow!(
                    "Overflowed while computing the size of the struct '{}/{struct_name}' - {member_type}",
                    stack.program_id()
                ))
            })?;
            // Return the size of the struct.
            Ok(size_of_name.saturating_add(size_of_members))
        }
        PlaintextType::Array(array_type) => {
            // Retrieve the number of elements in the array.
            let num_elements = **array_type.length() as u64;
            // Compute the size of an array element.
            let size_of_element = plaintext_size_in_bytes(stack, array_type.next_element_type())?;
            // Return the size of the array.
            Ok(num_elements.saturating_mul(size_of_element))
        }
    }
}

/// A helper function to compute the following: base_cost + (byte_multiplier * size_of_operands).
fn cost_in_size<'a, N: Network>(
    stack: &Stack<N>,
    finalize: &Finalize<N>,
    operands: impl IntoIterator<Item = &'a Operand<N>>,
    byte_multiplier: u64,
    base_cost: u64,
) -> Result<u64> {
    // Retrieve the finalize types.
    let finalize_types = stack.get_finalize_types(finalize.name())?;
    // Compute the size of the operands.
    let size_of_operands = operands.into_iter().try_fold(0u64, |acc, operand| {
        // Determine the size of the operand.
        let operand_size = match finalize_types.get_type_from_operand(stack, operand)? {
            FinalizeType::Plaintext(plaintext_type) => plaintext_size_in_bytes(stack, &plaintext_type)?,
            FinalizeType::Future(future) => {
                bail!("Future '{future}' is not a valid operand in the finalize scope");
            }
        };
        // Safely add the size to the accumulator.
        acc.checked_add(operand_size).ok_or(anyhow!(
            "Overflowed while computing the size of the operand '{operand}' in '{}/{}' (finalize)",
            stack.program_id(),
            finalize.name()
        ))
    })?;
    // Return the cost.
    Ok(base_cost.saturating_add(byte_multiplier.saturating_mul(size_of_operands)))
}

/// Returns the the cost of a command in a finalize scope.
pub fn cost_per_command<N: Network>(stack: &Stack<N>, finalize: &Finalize<N>, command: &Command<N>) -> Result<u64> {
    match command {
        Command::Instruction(Instruction::Abs(_)) => Ok(500),
        Command::Instruction(Instruction::AbsWrapped(_)) => Ok(500),
        Command::Instruction(Instruction::Add(_)) => Ok(500),
        Command::Instruction(Instruction::AddWrapped(_)) => Ok(500),
        Command::Instruction(Instruction::And(_)) => Ok(500),
        Command::Instruction(Instruction::AssertEq(_)) => Ok(500),
        Command::Instruction(Instruction::AssertNeq(_)) => Ok(500),
        Command::Instruction(Instruction::Async(_)) => bail!("'async' is not supported in finalize"),
        Command::Instruction(Instruction::Call(_)) => bail!("'call' is not supported in finalize"),
        Command::Instruction(Instruction::Cast(cast)) => match cast.cast_type() {
            CastType::Plaintext(PlaintextType::Literal(_)) => Ok(500),
            CastType::Plaintext(plaintext_type) => Ok(plaintext_size_in_bytes(stack, plaintext_type)?
                .saturating_mul(CAST_PER_BYTE_COST)
                .saturating_add(CAST_BASE_COST)),
            CastType::GroupXCoordinate
            | CastType::GroupYCoordinate
            | CastType::Record(_)
            | CastType::ExternalRecord(_) => Ok(500),
        },
        Command::Instruction(Instruction::CastLossy(cast_lossy)) => match cast_lossy.cast_type() {
            CastType::Plaintext(PlaintextType::Literal(_)) => Ok(500),
            CastType::Plaintext(plaintext_type) => Ok(plaintext_size_in_bytes(stack, plaintext_type)?
                .saturating_mul(CAST_PER_BYTE_COST)
                .saturating_add(CAST_BASE_COST)),
            CastType::GroupXCoordinate
            | CastType::GroupYCoordinate
            | CastType::Record(_)
            | CastType::ExternalRecord(_) => Ok(500),
        },
        Command::Instruction(Instruction::CommitBHP256(commit)) => {
            cost_in_size(stack, finalize, commit.operands(), HASH_BHP_PER_BYTE_COST, HASH_BHP_BASE_COST)
        }
        Command::Instruction(Instruction::CommitBHP512(commit)) => {
            cost_in_size(stack, finalize, commit.operands(), HASH_BHP_PER_BYTE_COST, HASH_BHP_BASE_COST)
        }
        Command::Instruction(Instruction::CommitBHP768(commit)) => {
            cost_in_size(stack, finalize, commit.operands(), HASH_BHP_PER_BYTE_COST, HASH_BHP_BASE_COST)
        }
        Command::Instruction(Instruction::CommitBHP1024(commit)) => {
            cost_in_size(stack, finalize, commit.operands(), HASH_BHP_PER_BYTE_COST, HASH_BHP_BASE_COST)
        }
        Command::Instruction(Instruction::CommitPED64(commit)) => {
            cost_in_size(stack, finalize, commit.operands(), HASH_PER_BYTE_COST, HASH_BASE_COST)
        }
        Command::Instruction(Instruction::CommitPED128(commit)) => {
            cost_in_size(stack, finalize, commit.operands(), HASH_PER_BYTE_COST, HASH_BASE_COST)
        }
        Command::Instruction(Instruction::Div(div)) => {
            // Ensure `div` has exactly two operands.
            ensure!(div.operands().len() == 2, "'div' must contain exactly 2 operands");
            // Retrieve the finalize types.
            let finalize_types = stack.get_finalize_types(finalize.name())?;
            // Retrieve the price by the operand type.
            match finalize_types.get_type_from_operand(stack, &div.operands()[0])? {
                FinalizeType::Plaintext(PlaintextType::Literal(LiteralType::Field)) => Ok(1_500),
                FinalizeType::Plaintext(PlaintextType::Literal(_)) => Ok(500),
                FinalizeType::Plaintext(PlaintextType::Array(_)) => bail!("'div' does not support arrays"),
                FinalizeType::Plaintext(PlaintextType::Struct(_)) => bail!("'div' does not support structs"),
                FinalizeType::Future(_) => bail!("'div' does not support futures"),
            }
        }
        Command::Instruction(Instruction::DivWrapped(_)) => Ok(500),
        Command::Instruction(Instruction::Double(_)) => Ok(500),
        Command::Instruction(Instruction::GreaterThan(_)) => Ok(500),
        Command::Instruction(Instruction::GreaterThanOrEqual(_)) => Ok(500),
        Command::Instruction(Instruction::HashBHP256(hash)) => {
            cost_in_size(stack, finalize, hash.operands(), HASH_BHP_PER_BYTE_COST, HASH_BHP_BASE_COST)
        }
        Command::Instruction(Instruction::HashBHP512(hash)) => {
            cost_in_size(stack, finalize, hash.operands(), HASH_BHP_PER_BYTE_COST, HASH_BHP_BASE_COST)
        }
        Command::Instruction(Instruction::HashBHP768(hash)) => {
            cost_in_size(stack, finalize, hash.operands(), HASH_BHP_PER_BYTE_COST, HASH_BHP_BASE_COST)
        }
        Command::Instruction(Instruction::HashBHP1024(hash)) => {
            cost_in_size(stack, finalize, hash.operands(), HASH_BHP_PER_BYTE_COST, HASH_BHP_BASE_COST)
        }
        Command::Instruction(Instruction::HashKeccak256(hash)) => {
            cost_in_size(stack, finalize, hash.operands(), HASH_PER_BYTE_COST, HASH_BASE_COST)
        }
        Command::Instruction(Instruction::HashKeccak384(hash)) => {
            cost_in_size(stack, finalize, hash.operands(), HASH_PER_BYTE_COST, HASH_BASE_COST)
        }
        Command::Instruction(Instruction::HashKeccak512(hash)) => {
            cost_in_size(stack, finalize, hash.operands(), HASH_PER_BYTE_COST, HASH_BASE_COST)
        }
        Command::Instruction(Instruction::HashPED64(hash)) => {
            cost_in_size(stack, finalize, hash.operands(), HASH_PER_BYTE_COST, HASH_BASE_COST)
        }
        Command::Instruction(Instruction::HashPED128(hash)) => {
            cost_in_size(stack, finalize, hash.operands(), HASH_PER_BYTE_COST, HASH_BASE_COST)
        }
        Command::Instruction(Instruction::HashPSD2(hash)) => {
            cost_in_size(stack, finalize, hash.operands(), HASH_PSD_PER_BYTE_COST, HASH_PSD_BASE_COST)
        }
        Command::Instruction(Instruction::HashPSD4(hash)) => {
            cost_in_size(stack, finalize, hash.operands(), HASH_PSD_PER_BYTE_COST, HASH_PSD_BASE_COST)
        }
        Command::Instruction(Instruction::HashPSD8(hash)) => {
            cost_in_size(stack, finalize, hash.operands(), HASH_PSD_PER_BYTE_COST, HASH_PSD_BASE_COST)
        }
        Command::Instruction(Instruction::HashSha3_256(hash)) => {
            cost_in_size(stack, finalize, hash.operands(), HASH_PER_BYTE_COST, HASH_BASE_COST)
        }
        Command::Instruction(Instruction::HashSha3_384(hash)) => {
            cost_in_size(stack, finalize, hash.operands(), HASH_PER_BYTE_COST, HASH_BASE_COST)
        }
        Command::Instruction(Instruction::HashSha3_512(hash)) => {
            cost_in_size(stack, finalize, hash.operands(), HASH_PER_BYTE_COST, HASH_BASE_COST)
        }
        Command::Instruction(Instruction::HashManyPSD2(_)) => {
            bail!("`hash_many.psd2` is not supported in finalize")
        }
        Command::Instruction(Instruction::HashManyPSD4(_)) => {
            bail!("`hash_many.psd4` is not supported in finalize")
        }
        Command::Instruction(Instruction::HashManyPSD8(_)) => {
            bail!("`hash_many.psd8` is not supported in finalize")
        }
        Command::Instruction(Instruction::Inv(_)) => Ok(2_500),
        Command::Instruction(Instruction::IsEq(_)) => Ok(500),
        Command::Instruction(Instruction::IsNeq(_)) => Ok(500),
        Command::Instruction(Instruction::LessThan(_)) => Ok(500),
        Command::Instruction(Instruction::LessThanOrEqual(_)) => Ok(500),
        Command::Instruction(Instruction::Modulo(_)) => Ok(500),
        Command::Instruction(Instruction::Mul(mul)) => {
            // Ensure `mul` has exactly two operands.
            ensure!(mul.operands().len() == 2, "'mul' must contain exactly 2 operands");
            // Retrieve the finalize types.
            let finalize_types = stack.get_finalize_types(finalize.name())?;
            // Retrieve the price by operand type.
            match finalize_types.get_type_from_operand(stack, &mul.operands()[0])? {
                FinalizeType::Plaintext(PlaintextType::Literal(LiteralType::Group)) => Ok(10_000),
                FinalizeType::Plaintext(PlaintextType::Literal(LiteralType::Scalar)) => Ok(10_000),
                FinalizeType::Plaintext(PlaintextType::Literal(_)) => Ok(500),
                FinalizeType::Plaintext(PlaintextType::Array(_)) => bail!("'mul' does not support arrays"),
                FinalizeType::Plaintext(PlaintextType::Struct(_)) => bail!("'mul' does not support structs"),
                FinalizeType::Future(_) => bail!("'mul' does not support futures"),
            }
        }
        Command::Instruction(Instruction::MulWrapped(_)) => Ok(500),
        Command::Instruction(Instruction::Nand(_)) => Ok(500),
        Command::Instruction(Instruction::Neg(_)) => Ok(500),
        Command::Instruction(Instruction::Nor(_)) => Ok(500),
        Command::Instruction(Instruction::Not(_)) => Ok(500),
        Command::Instruction(Instruction::Or(_)) => Ok(500),
        Command::Instruction(Instruction::Pow(pow)) => {
            // Ensure `pow` has at least one operand.
            ensure!(!pow.operands().is_empty(), "'pow' must contain at least 1 operand");
            // Retrieve the finalize types.
            let finalize_types = stack.get_finalize_types(finalize.name())?;
            // Retrieve the price by operand type.
            match finalize_types.get_type_from_operand(stack, &pow.operands()[0])? {
                FinalizeType::Plaintext(PlaintextType::Literal(LiteralType::Field)) => Ok(1_500),
                FinalizeType::Plaintext(PlaintextType::Literal(_)) => Ok(500),
                FinalizeType::Plaintext(PlaintextType::Array(_)) => bail!("'pow' does not support arrays"),
                FinalizeType::Plaintext(PlaintextType::Struct(_)) => bail!("'pow' does not support structs"),
                FinalizeType::Future(_) => bail!("'pow' does not support futures"),
            }
        }
        Command::Instruction(Instruction::PowWrapped(_)) => Ok(500),
        Command::Instruction(Instruction::Rem(_)) => Ok(500),
        Command::Instruction(Instruction::RemWrapped(_)) => Ok(500),
        Command::Instruction(Instruction::SignVerify(sign)) => {
            cost_in_size(stack, finalize, sign.operands(), HASH_PSD_PER_BYTE_COST, HASH_PSD_BASE_COST)
        }
        Command::Instruction(Instruction::Shl(_)) => Ok(500),
        Command::Instruction(Instruction::ShlWrapped(_)) => Ok(500),
        Command::Instruction(Instruction::Shr(_)) => Ok(500),
        Command::Instruction(Instruction::ShrWrapped(_)) => Ok(500),
        Command::Instruction(Instruction::Square(_)) => Ok(500),
        Command::Instruction(Instruction::SquareRoot(_)) => Ok(2_500),
        Command::Instruction(Instruction::Sub(_)) => Ok(500),
        Command::Instruction(Instruction::SubWrapped(_)) => Ok(500),
        Command::Instruction(Instruction::Ternary(_)) => Ok(500),
        Command::Instruction(Instruction::Xor(_)) => Ok(500),
        Command::Await(_) => Ok(500),
        Command::Contains(command) => {
            cost_in_size(stack, finalize, [command.key()], MAPPING_PER_BYTE_COST, MAPPING_BASE_COST)
        }
        Command::Get(command) => {
            cost_in_size(stack, finalize, [command.key()], MAPPING_PER_BYTE_COST, MAPPING_BASE_COST)
        }
        Command::GetOrUse(command) => {
            cost_in_size(stack, finalize, [command.key()], MAPPING_PER_BYTE_COST, MAPPING_BASE_COST)
        }
        Command::RandChaCha(_) => Ok(25_000),
        Command::Remove(_) => Ok(MAPPING_BASE_COST),
        Command::Set(command) => {
            cost_in_size(stack, finalize, [command.key(), command.value()], SET_PER_BYTE_COST, SET_BASE_COST)
        }
        Command::BranchEq(_) | Command::BranchNeq(_) => Ok(500),
        Command::Position(_) => Ok(100),
    }
}

/// Returns the minimum number of microcredits required to run the finalize.
pub fn cost_in_microcredits<N: Network>(stack: &Stack<N>, function_name: &Identifier<N>) -> Result<u64> {
    // Retrieve the finalize logic.
    let Some(finalize) = stack.get_function_ref(function_name)?.finalize_logic() else {
        // Return a finalize cost of 0, if the function does not have a finalize scope.
        return Ok(0);
    };
    // Get the cost of finalizing all futures.
    let mut future_cost = 0u64;
    for input in finalize.inputs() {
        if let FinalizeType::Future(future) = input.finalize_type() {
            // Get the external stack for the future.
            let stack = stack.get_external_stack(future.program_id())?;
            // Accumulate the finalize cost of the future.
            future_cost = future_cost
                .checked_add(stack.get_finalize_cost(future.resource())?)
                .ok_or(anyhow!("Finalize cost overflowed"))?;
        }
    }
    // Aggregate the cost of all commands in the program.
    finalize
        .commands()
        .iter()
        .map(|command| cost_per_command(stack, finalize, command))
        .try_fold(future_cost, |acc, res| {
            res.and_then(|x| acc.checked_add(x).ok_or(anyhow!("Finalize cost overflowed")))
        })
}
