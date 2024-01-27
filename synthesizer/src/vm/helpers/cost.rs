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

use crate::{
    prelude::{Stack, StackProgramTypes},
    VM,
};
use console::{
    prelude::*,
    program::{FinalizeType, Identifier, LiteralType, PlaintextType},
};
use ledger_block::{Deployment, Execution};
use ledger_store::ConsensusStorage;
use synthesizer_program::{CastType, Command, Instruction, Operand, StackProgram};

// Finalize costs for compute heavy operations. Used as BASE_COST + PER_BYTE_COST * SIZE_IN_BYTES.

const CAST_COMMAND_BASE_COST: u64 = 500;
const CAST_PER_BYTE_COST: u64 = 30;

const GET_COMMAND_BASE_COST: u64 = 10_000;
const GET_COMMAND_PER_BYTE_COST: u64 = 10;

const HASH_BASE_COST: u64 = 10_000;
const HASH_PER_BYTE_COST: u64 = 30;

const HASH_BHP_BASE_COST: u64 = 50_000;
const HASH_BHP_PER_BYTE_COST: u64 = 300;

const HASH_PSD_BASE_COST: u64 = 40_000;
const HASH_PSD_PER_BYTE_COST: u64 = 75;

const SET_COMMAND_BASE_COST: u64 = 10_000;
const SET_COMMAND_PER_BYTE_COST: u64 = 100;

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

    // Compute the finalize cost in microcredits.
    let mut finalize_cost = 0u64;
    // Iterate over the transitions to accumulate the finalize cost.
    for transition in execution.transitions() {
        // Retrieve the program ID and function name.
        let (program_id, function_name) = (transition.program_id(), transition.function_name());
        // Retrieve the finalize cost.
        let cost = cost_in_microcredits(vm.process().read().get_stack(program_id)?, function_name)?;
        // Accumulate the finalize cost.
        if cost > 0 {
            finalize_cost = finalize_cost
                .checked_add(cost)
                .ok_or(anyhow!("The finalize cost computation overflowed on '{program_id}/{function_name}'"))?;
        }
    }

    // Compute the total cost in microcredits.
    let total_cost = storage_cost
        .checked_add(finalize_cost)
        .ok_or(anyhow!("The total cost computation overflowed for an execution"))?;

    Ok((total_cost, (storage_cost, finalize_cost)))
}

/// Returns the minimum number of microcredits required to run the finalize.
pub fn cost_in_microcredits<N: Network>(stack: &Stack<N>, function_name: &Identifier<N>) -> Result<u64> {
    // Retrieve the finalize logic.
    let Some(finalize) = stack.get_function_ref(function_name)?.finalize_logic() else {
        // Return a finalize cost of 0, if the function does not have a finalize scope.
        return Ok(0);
    };

    // Retrieve the finalize types.
    let finalize_types = stack.get_finalize_types(finalize.name())?;

    // Helper function to get the size of the operand type.
    let operand_size_in_bytes = |operand: &Operand<N>| {
        // Get the finalize type from the operand.
        let finalize_type = finalize_types.get_type_from_operand(stack, operand)?;

        // Get the plaintext type from the finalize type.
        let plaintext_type = match finalize_type {
            FinalizeType::Plaintext(plaintext_type) => plaintext_type,
            FinalizeType::Future(_) => bail!("`Future` types are not supported in storage cost computation."),
        };

        // Get the size of the operand type.
        plaintext_size_in_bytes(stack, &plaintext_type)
    };

    let size_cost = |operands: &[Operand<N>], byte_multiplier: u64, base_cost: u64| {
        let operand_size = operands.iter().map(operand_size_in_bytes).sum::<Result<u64>>()?;
        Ok(base_cost.saturating_add(operand_size.saturating_mul(byte_multiplier)))
    };

    // Measure the cost of each command.
    let cost = |command: &Command<N>| match command {
        Command::Instruction(Instruction::Abs(_)) => Ok(500),
        Command::Instruction(Instruction::AbsWrapped(_)) => Ok(500),
        Command::Instruction(Instruction::Add(_)) => Ok(500),
        Command::Instruction(Instruction::AddWrapped(_)) => Ok(500),
        Command::Instruction(Instruction::And(_)) => Ok(500),
        Command::Instruction(Instruction::AssertEq(_)) => Ok(500),
        Command::Instruction(Instruction::AssertNeq(_)) => Ok(500),
        Command::Instruction(Instruction::Async(_)) => bail!("`async` is not supported in finalize."),
        Command::Instruction(Instruction::Call(_)) => bail!("`call` is not supported in finalize."),
        Command::Instruction(Instruction::Cast(cast)) => {
            let cast_type = cast.cast_type();

            // Get the price by operand type.
            match cast_type {
                CastType::Plaintext(PlaintextType::Literal(_)) => Ok(500),
                CastType::Plaintext(plaintext_type) => Ok(plaintext_size_in_bytes(stack, plaintext_type)?
                    .saturating_mul(CAST_PER_BYTE_COST)
                    .saturating_add(CAST_COMMAND_BASE_COST)),
                _ => Ok(500),
            }
        }
        Command::Instruction(Instruction::CastLossy(cast_lossy)) => {
            let cast_type = cast_lossy.cast_type();

            // Get the price by operand type.
            match cast_type {
                CastType::Plaintext(PlaintextType::Literal(_)) => Ok(500),
                CastType::Plaintext(plaintext_type) => Ok(plaintext_size_in_bytes(stack, plaintext_type)?
                    .saturating_mul(CAST_PER_BYTE_COST)
                    .saturating_add(CAST_COMMAND_BASE_COST)),
                _ => Ok(500),
            }
        }
        Command::Instruction(Instruction::CommitBHP256(commit)) => {
            size_cost(commit.operands(), HASH_BHP_PER_BYTE_COST, HASH_BHP_BASE_COST)
        }
        Command::Instruction(Instruction::CommitBHP512(commit)) => {
            size_cost(commit.operands(), HASH_BHP_PER_BYTE_COST, HASH_BHP_BASE_COST)
        }
        Command::Instruction(Instruction::CommitBHP768(commit)) => {
            size_cost(commit.operands(), HASH_BHP_PER_BYTE_COST, HASH_BHP_BASE_COST)
        }
        Command::Instruction(Instruction::CommitBHP1024(commit)) => {
            size_cost(commit.operands(), HASH_BHP_PER_BYTE_COST, HASH_BHP_BASE_COST)
        }
        Command::Instruction(Instruction::CommitPED64(commit)) => {
            size_cost(commit.operands(), HASH_PER_BYTE_COST, HASH_BASE_COST)
        }
        Command::Instruction(Instruction::CommitPED128(commit)) => {
            size_cost(commit.operands(), HASH_PER_BYTE_COST, HASH_BASE_COST)
        }
        Command::Instruction(Instruction::Div(div)) => {
            let operands = div.operands();
            ensure!(operands.len() == 2, "div opcode must have exactly two operands.");

            // Get the price by operand type.
            let operand_type = finalize_types.get_type_from_operand(stack, &operands[0])?;
            match operand_type {
                FinalizeType::Plaintext(PlaintextType::Literal(LiteralType::Field)) => Ok(1_500),
                FinalizeType::Plaintext(PlaintextType::Literal(_)) => Ok(500),
                FinalizeType::Plaintext(PlaintextType::Array(_)) => bail!("div opcode does not support arrays."),
                FinalizeType::Plaintext(PlaintextType::Struct(_)) => bail!("div opcode does not support structs."),
                _ => bail!("div opcode does not support futures."),
            }
        }
        Command::Instruction(Instruction::DivWrapped(_)) => Ok(500),
        Command::Instruction(Instruction::Double(_)) => Ok(500),
        Command::Instruction(Instruction::GreaterThan(_)) => Ok(500),
        Command::Instruction(Instruction::GreaterThanOrEqual(_)) => Ok(500),
        Command::Instruction(Instruction::HashBHP256(hash)) => {
            size_cost(hash.operands(), HASH_BHP_PER_BYTE_COST, HASH_BHP_BASE_COST)
        }
        Command::Instruction(Instruction::HashBHP512(hash)) => {
            size_cost(hash.operands(), HASH_BHP_PER_BYTE_COST, HASH_BHP_BASE_COST)
        }
        Command::Instruction(Instruction::HashBHP768(hash)) => {
            size_cost(hash.operands(), HASH_BHP_PER_BYTE_COST, HASH_BHP_BASE_COST)
        }
        Command::Instruction(Instruction::HashBHP1024(hash)) => {
            size_cost(hash.operands(), HASH_BHP_PER_BYTE_COST, HASH_BHP_BASE_COST)
        }
        Command::Instruction(Instruction::HashKeccak256(hash)) => {
            size_cost(hash.operands(), HASH_PER_BYTE_COST, HASH_BASE_COST)
        }
        Command::Instruction(Instruction::HashKeccak384(hash)) => {
            size_cost(hash.operands(), HASH_PER_BYTE_COST, HASH_BASE_COST)
        }
        Command::Instruction(Instruction::HashKeccak512(hash)) => {
            size_cost(hash.operands(), HASH_PER_BYTE_COST, HASH_BASE_COST)
        }
        Command::Instruction(Instruction::HashPED64(hash)) => {
            size_cost(hash.operands(), HASH_PER_BYTE_COST, HASH_BASE_COST)
        }
        Command::Instruction(Instruction::HashPED128(hash)) => {
            size_cost(hash.operands(), HASH_PER_BYTE_COST, HASH_BASE_COST)
        }
        Command::Instruction(Instruction::HashPSD2(hash)) => {
            size_cost(hash.operands(), HASH_PSD_PER_BYTE_COST, HASH_PSD_BASE_COST)
        }
        Command::Instruction(Instruction::HashPSD4(hash)) => {
            size_cost(hash.operands(), HASH_PSD_PER_BYTE_COST, HASH_PSD_BASE_COST)
        }
        Command::Instruction(Instruction::HashPSD8(hash)) => {
            size_cost(hash.operands(), HASH_PSD_PER_BYTE_COST, HASH_PSD_BASE_COST)
        }
        Command::Instruction(Instruction::HashSha3_256(hash)) => {
            size_cost(hash.operands(), HASH_PER_BYTE_COST, HASH_BASE_COST)
        }
        Command::Instruction(Instruction::HashSha3_384(hash)) => {
            size_cost(hash.operands(), HASH_PER_BYTE_COST, HASH_BASE_COST)
        }
        Command::Instruction(Instruction::HashSha3_512(hash)) => {
            size_cost(hash.operands(), HASH_PER_BYTE_COST, HASH_BASE_COST)
        }
        Command::Instruction(Instruction::HashManyPSD2(_)) => {
            bail!("`hash_many.psd2` is not supported in finalize.")
        }
        Command::Instruction(Instruction::HashManyPSD4(_)) => {
            bail!("`hash_many.psd4` is not supported in finalize.")
        }
        Command::Instruction(Instruction::HashManyPSD8(_)) => {
            bail!("`hash_many.psd8` is not supported in finalize.")
        }
        Command::Instruction(Instruction::Inv(_)) => Ok(1_000),
        Command::Instruction(Instruction::IsEq(_)) => Ok(500),
        Command::Instruction(Instruction::IsNeq(_)) => Ok(500),
        Command::Instruction(Instruction::LessThan(_)) => Ok(500),
        Command::Instruction(Instruction::LessThanOrEqual(_)) => Ok(500),
        Command::Instruction(Instruction::Modulo(_)) => Ok(500),
        Command::Instruction(Instruction::Mul(mul)) => {
            let operands = mul.operands();
            ensure!(operands.len() == 2, "mul opcode must have exactly two operands.");

            // Get the price by operand type.
            let operand_type = finalize_types.get_type_from_operand(stack, &operands[0])?;
            match operand_type {
                FinalizeType::Plaintext(PlaintextType::Literal(LiteralType::Group)) => Ok(10_000),
                FinalizeType::Plaintext(PlaintextType::Literal(LiteralType::Scalar)) => Ok(10_000),
                FinalizeType::Plaintext(PlaintextType::Literal(_)) => Ok(500),
                FinalizeType::Plaintext(PlaintextType::Array(_)) => bail!("mul opcode does not support arrays."),
                FinalizeType::Plaintext(PlaintextType::Struct(_)) => bail!("mul opcode does not support structs."),
                _ => bail!("mul opcode does not support futures."),
            }
        }
        Command::Instruction(Instruction::MulWrapped(_)) => Ok(500),
        Command::Instruction(Instruction::Nand(_)) => Ok(500),
        Command::Instruction(Instruction::Neg(_)) => Ok(500),
        Command::Instruction(Instruction::Nor(_)) => Ok(500),
        Command::Instruction(Instruction::Not(_)) => Ok(500),
        Command::Instruction(Instruction::Or(_)) => Ok(500),
        Command::Instruction(Instruction::Pow(pow)) => {
            let operands = pow.operands();
            ensure!(!operands.is_empty(), "pow opcode must have at least one operand.");

            // Get the price by operand type.
            let operand_type = finalize_types.get_type_from_operand(stack, &operands[0])?;
            match operand_type {
                FinalizeType::Plaintext(PlaintextType::Literal(LiteralType::Field)) => Ok(1_500),
                FinalizeType::Plaintext(PlaintextType::Literal(_)) => Ok(500),
                FinalizeType::Plaintext(PlaintextType::Array(_)) => bail!("pow opcode does not support arrays."),
                FinalizeType::Plaintext(PlaintextType::Struct(_)) => bail!("pow opcode does not support structs."),
                _ => bail!("pow opcode does not support futures."),
            }
        }
        Command::Instruction(Instruction::PowWrapped(_)) => Ok(500),
        Command::Instruction(Instruction::Rem(_)) => Ok(500),
        Command::Instruction(Instruction::RemWrapped(_)) => Ok(500),
        Command::Instruction(Instruction::SignVerify(_)) => Ok(HASH_PSD_BASE_COST),
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
        Command::Contains(contains) => Ok(operand_size_in_bytes(contains.key())?
            .saturating_mul(GET_COMMAND_PER_BYTE_COST)
            .saturating_add(GET_COMMAND_BASE_COST)),
        Command::Get(get) => Ok(operand_size_in_bytes(get.key())?
            .saturating_mul(GET_COMMAND_PER_BYTE_COST)
            .saturating_add(GET_COMMAND_BASE_COST)),
        Command::GetOrUse(get) => Ok(operand_size_in_bytes(get.key())?
            .saturating_mul(GET_COMMAND_PER_BYTE_COST)
            .saturating_add(GET_COMMAND_BASE_COST)),
        Command::RandChaCha(_) => Ok(25_000),
        Command::Remove(_) => Ok(GET_COMMAND_BASE_COST),
        Command::Set(set) => Ok(operand_size_in_bytes(set.key())?
            .saturating_add(operand_size_in_bytes(set.value())?)
            .saturating_mul(SET_COMMAND_PER_BYTE_COST)
            .saturating_add(SET_COMMAND_BASE_COST)),
        Command::BranchEq(_) | Command::BranchNeq(_) => Ok(500),
        Command::Position(_) => Ok(100),
    };

    // Aggregate the cost of all commands in the program.
    finalize
        .commands()
        .iter()
        .map(cost)
        .try_fold(0u64, |acc, res| res.and_then(|x| acc.checked_add(x).ok_or(anyhow!("Finalize cost overflowed"))))
}

// Helper function to get the plaintext type in bytes.
fn plaintext_size_in_bytes<N: Network>(stack: &Stack<N>, plaintext_type: &PlaintextType<N>) -> Result<u64> {
    match plaintext_type {
        PlaintextType::Literal(literal_type) => Ok(literal_type.size_in_bytes::<N>() as u64),
        PlaintextType::Struct(struct_identifier) => {
            // Retrieve the struct from the stack.
            let plaintext_struct = stack.program().get_struct(struct_identifier)?;

            // Retrieve the size of the struct identifier.
            let identifier_size = plaintext_struct.name().to_bytes_le()?.len() as u64;

            // Retrieve the size of all the members of the struct.
            let size_of_members = plaintext_struct
                .members()
                .iter()
                .map(|(_, member_type)| plaintext_size_in_bytes(stack, member_type))
                .sum::<Result<u64>>()?;

            // Return the size of the struct.
            Ok(identifier_size.saturating_add(size_of_members))
        }
        PlaintextType::Array(array_type) => {
            // Retrieve the number of elements in the array.
            let num_array_elements = **array_type.length() as u64;

            // Retrieve the size of the internal array types.
            Ok(num_array_elements.saturating_mul(plaintext_size_in_bytes(stack, array_type.next_element_type())?))
        }
    }
}
