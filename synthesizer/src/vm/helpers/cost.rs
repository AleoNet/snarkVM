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
    program::{FinalizeType, LiteralType, PlaintextType},
};
use ledger_block::{Deployment, Execution};
use ledger_store::ConsensusStorage;
use synthesizer_program::{Command, Finalize, Instruction, Operand, StackProgram};

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
        let cost = match program.get_function(function_name)?.finalize_logic() {
            Some(finalize) => cost_in_microcredits(vm.process().read().get_stack(program.id())?, finalize)?,
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
pub fn cost_in_microcredits<N: Network>(stack: &Stack<N>, finalize: &Finalize<N>) -> Result<u64> {
    // Retrieve the finalize types.
    let finalize_types = stack.get_finalize_types(finalize.name())?;

    // Helper function to get the plaintext type in bytes
    fn plaintext_size_in_bytes<N: Network>(stack: &Stack<N>, plaintext_type: &PlaintextType<N>) -> Result<u64> {
        match plaintext_type {
            PlaintextType::Literal(literal_type) => {
                // Retrieve the literal size in bits.
                let literal_size_in_bits = literal_type.size_in_bits::<N>() as u64;

                // Compute the size in bytes.
                let literal_size_in_bytes = literal_size_in_bits.saturating_add(7).saturating_div(8);

                // Return the size of the literal.
                Ok(literal_size_in_bytes)
            }
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
                // Retrieve the number of elements in the array
                let num_array_elements = **array_type.length() as u64;

                // Retrieve the size of the internal array types.
                Ok(num_array_elements.saturating_mul(plaintext_size_in_bytes(stack, array_type.next_element_type())?))
            }
        }
    }

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

    // Defines the cost of each command.
    let cost = |command: &Command<N>| match command {
        Command::Instruction(Instruction::Abs(_)) => Ok(2_000),
        Command::Instruction(Instruction::AbsWrapped(_)) => Ok(2_000),
        Command::Instruction(Instruction::Add(_)) => Ok(2_000),
        Command::Instruction(Instruction::AddWrapped(_)) => Ok(2_000),
        Command::Instruction(Instruction::And(_)) => Ok(2_000),
        Command::Instruction(Instruction::AssertEq(_)) => Ok(2_000),
        Command::Instruction(Instruction::AssertNeq(_)) => Ok(2_000),
        Command::Instruction(Instruction::Async(_)) => bail!("`async` is not supported in finalize."),
        Command::Instruction(Instruction::Call(_)) => bail!("`call` is not supported in finalize."),
        Command::Instruction(Instruction::Cast(_)) => Ok(2_000),
        Command::Instruction(Instruction::CastLossy(_)) => Ok(2_000),
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
        Command::Instruction(Instruction::HashBHP256(_)) => Ok(100_000),
        Command::Instruction(Instruction::HashBHP512(_)) => Ok(100_000),
        Command::Instruction(Instruction::HashBHP768(_)) => Ok(100_000),
        Command::Instruction(Instruction::HashBHP1024(_)) => Ok(100_000),
        Command::Instruction(Instruction::HashKeccak256(_)) => Ok(100_000),
        Command::Instruction(Instruction::HashKeccak384(_)) => Ok(100_000),
        Command::Instruction(Instruction::HashKeccak512(_)) => Ok(100_000),
        Command::Instruction(Instruction::HashPED64(_)) => Ok(20_000),
        Command::Instruction(Instruction::HashPED128(_)) => Ok(30_000),
        Command::Instruction(Instruction::HashPSD2(hash)) => match hash.destination_type() {
            PlaintextType::Literal(LiteralType::Address) | PlaintextType::Literal(LiteralType::Group) => Ok(600_000),
            PlaintextType::Literal(..) => Ok(60_000),
            plaintext_type => bail!("`hash.psd2` is not supported for plaintext type '{plaintext_type}'"),
        },
        Command::Instruction(Instruction::HashPSD4(hash)) => match hash.destination_type() {
            PlaintextType::Literal(LiteralType::Address) | PlaintextType::Literal(LiteralType::Group) => Ok(700_000),
            PlaintextType::Literal(..) => Ok(100_000),
            plaintext_type => bail!("`hash.psd4` is not supported for plaintext type '{plaintext_type}'"),
        },
        Command::Instruction(Instruction::HashPSD8(hash)) => match hash.destination_type() {
            PlaintextType::Literal(LiteralType::Address) | PlaintextType::Literal(LiteralType::Group) => Ok(800_000),
            PlaintextType::Literal(..) => Ok(200_000),
            plaintext_type => bail!("`hash.psd8` is not supported for plaintext type '{plaintext_type}'"),
        },
        Command::Instruction(Instruction::HashSha3_256(_)) => Ok(100_000),
        Command::Instruction(Instruction::HashSha3_384(_)) => Ok(100_000),
        Command::Instruction(Instruction::HashSha3_512(_)) => Ok(100_000),
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
        Command::Instruction(Instruction::SignVerify(_)) => Ok(250_000),
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
        Command::Await(_) => Ok(2_000),
        Command::Contains(_) => Ok(12_500),
        Command::Get(_) => Ok(25_000),
        Command::GetOrUse(_) => Ok(25_000),
        Command::RandChaCha(_) => Ok(25_000),
        Command::Remove(_) => Ok(10_000),
        Command::Set(set) => {
            // TODO (raychu86): Adjust this multiplier.
            // The cost in microcredits per byte of storage used by the `set` command.
            const SET_COMMAND_BYTE_MULTIPLIER: u64 = 1000;

            // Get the size in bytes of the key and value types.
            let key_size_in_bytes = operand_size_in_bytes(set.key())?;
            let value_size_in_bytes = operand_size_in_bytes(set.value())?;

            // Calculate the size in bytes of the key and value.
            let stored_size_in_bytes = key_size_in_bytes.saturating_add(value_size_in_bytes);

            // Calculate the cost.
            Ok(stored_size_in_bytes.saturating_mul(SET_COMMAND_BYTE_MULTIPLIER))
        }
        Command::BranchEq(_) | Command::BranchNeq(_) => Ok(5_000),
        Command::Position(_) => Ok(1_000),
    };
    finalize
        .commands()
        .iter()
        .map(cost)
        .try_fold(0u64, |acc, res| res.and_then(|x| acc.checked_add(x).ok_or(anyhow!("Finalize cost overflowed"))))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{vm::test_helpers::CurrentNetwork, Process, Program};
    use circuit::network::AleoV0;
    use console::program::Identifier;

    #[test]
    fn test_credits_finalize_costs() {
        // Get the credits.aleo program.
        let program = Program::<CurrentNetwork>::credits().unwrap();

        // Load the process.
        let process = Process::<CurrentNetwork>::load().unwrap();

        // Get the stack.
        let stack = process.get_stack(program.id()).unwrap();

        // Function: `bond_public`
        let function = program.get_function(&Identifier::from_str("bond_public").unwrap()).unwrap();
        let finalize_cost = cost_in_microcredits(stack, function.finalize_logic().unwrap()).unwrap();
        assert_eq!(602500, finalize_cost);

        // Function: `unbond_public`
        let function = program.get_function(&Identifier::from_str("unbond_public").unwrap()).unwrap();
        let finalize_cost = cost_in_microcredits(stack, function.finalize_logic().unwrap()).unwrap();
        assert_eq!(897500, finalize_cost);

        // Function: `unbond_delegator_as_validator`
        let function = program.get_function(&Identifier::from_str("unbond_delegator_as_validator").unwrap()).unwrap();
        let finalize_cost = cost_in_microcredits(stack, function.finalize_logic().unwrap()).unwrap();
        assert_eq!(237500, finalize_cost);

        // Function `claim_unbond_public`
        let function = program.get_function(&Identifier::from_str("claim_unbond_public").unwrap()).unwrap();
        let finalize_cost = cost_in_microcredits(stack, function.finalize_logic().unwrap()).unwrap();
        assert_eq!(106000, finalize_cost);

        // Function `set_validator_state`
        let function = program.get_function(&Identifier::from_str("set_validator_state").unwrap()).unwrap();
        let finalize_cost = cost_in_microcredits(stack, function.finalize_logic().unwrap()).unwrap();
        assert_eq!(84000, finalize_cost);

        // Function: `transfer_public`
        let function = program.get_function(&Identifier::from_str("transfer_public").unwrap()).unwrap();
        let finalize_cost = cost_in_microcredits(stack, function.finalize_logic().unwrap()).unwrap();
        assert_eq!(142000, finalize_cost);

        // Function: `transfer_private`
        let function = program.get_function(&Identifier::from_str("transfer_private").unwrap()).unwrap();
        assert!(function.finalize_logic().is_none());

        // Function: `transfer_private_to_public`
        let function = program.get_function(&Identifier::from_str("transfer_private_to_public").unwrap()).unwrap();
        let finalize_cost = cost_in_microcredits(stack, function.finalize_logic().unwrap()).unwrap();
        assert_eq!(67000, finalize_cost);

        // Function: `transfer_public_to_private`
        let function = program.get_function(&Identifier::from_str("transfer_public_to_private").unwrap()).unwrap();
        let finalize_cost = cost_in_microcredits(stack, function.finalize_logic().unwrap()).unwrap();
        assert_eq!(75000, finalize_cost);

        // Function: `join`
        let function = program.get_function(&Identifier::from_str("join").unwrap()).unwrap();
        assert!(function.finalize_logic().is_none());

        // Function: `split`
        let function = program.get_function(&Identifier::from_str("split").unwrap()).unwrap();
        assert!(function.finalize_logic().is_none());

        // Function: `fee_private`
        let function = program.get_function(&Identifier::from_str("fee_private").unwrap()).unwrap();
        assert!(function.finalize_logic().is_none());

        // Function: `fee_public`
        let function = program.get_function(&Identifier::from_str("fee_public").unwrap()).unwrap();
        let finalize_cost = cost_in_microcredits(stack, function.finalize_logic().unwrap()).unwrap();
        assert_eq!(75000, finalize_cost);
    }

    #[test]
    fn test_finalize_costs_structs() {
        let rng = &mut TestRng::default();

        // Define a program
        let program_str = r"
program test_program.aleo;
struct small:
    a as u64;
    b as u64;
    c as u64;
struct medium:
    a as small;
    b as small;
    c as small;
struct large:
    a as medium;
    b as medium;
    c as medium;
struct xlarge:
    a as large;
    b as large;
    c as large;
mapping storage_small:
    key as u64.public;
    value as small.public;
mapping storage_medium:
    key as u64.public;
    value as medium.public;
mapping storage_large:
    key as u64.public;
    value as large.public;
mapping storage_xlarge:
    key as u64.public;
    value as xlarge.public;
function store_small:
    input r0 as u64.public;
    input r1 as small.public;
    async store_small r0 r1 into r2;
    output r2 as test_program.aleo/store_small.future;
finalize store_small:
    input r0 as u64.public;
    input r1 as small.public;
    set r1 into storage_small[r0];
function store_medium:
    input r0 as u64.public;
    input r1 as medium.public;
    async store_medium r0 r1 into r2;
    output r2 as test_program.aleo/store_medium.future;
finalize store_medium:
    input r0 as u64.public;
    input r1 as medium.public;
    set r1 into storage_medium[r0];
function store_large:
    input r0 as u64.public;
    input r1 as large.public;
    async store_large r0 r1 into r2;
    output r2 as test_program.aleo/store_large.future;
finalize store_large:
    input r0 as u64.public;
    input r1 as large.public;
    set r1 into storage_large[r0];
function store_xlarge:
    input r0 as u64.public;
    input r1 as xlarge.public;
    async store_xlarge r0 r1 into r2;
    output r2 as test_program.aleo/store_xlarge.future;
finalize store_xlarge:
    input r0 as u64.public;
    input r1 as xlarge.public;
    set r1 into storage_xlarge[r0];
        ";

        // Compile the program.
        let program = Program::<CurrentNetwork>::from_str(program_str).unwrap();

        // Load the process.
        let mut process = Process::<CurrentNetwork>::load().unwrap();

        // Deploy and load the program.
        let deployment = process.deploy::<AleoV0, _>(&program, rng).unwrap();
        process.load_deployment(&deployment).unwrap();

        // Get the stack.
        let stack = process.get_stack(program.id()).unwrap();

        // Test the price of each execution.

        // Function: `store_small`
        let function = program.get_function(&Identifier::from_str("store_small").unwrap()).unwrap();
        let finalize_cost = cost_in_microcredits(stack, function.finalize_logic().unwrap()).unwrap();
        assert_eq!(38000, finalize_cost);

        // Function: `store_medium`
        let function = program.get_function(&Identifier::from_str("store_medium").unwrap()).unwrap();
        let finalize_cost = cost_in_microcredits(stack, function.finalize_logic().unwrap()).unwrap();
        assert_eq!(105000, finalize_cost);

        // Function: `store_large`
        let function = program.get_function(&Identifier::from_str("store_large").unwrap()).unwrap();
        let finalize_cost = cost_in_microcredits(stack, function.finalize_logic().unwrap()).unwrap();
        assert_eq!(305000, finalize_cost);

        // Function: `store_xlarge`
        let function = program.get_function(&Identifier::from_str("store_xlarge").unwrap()).unwrap();
        let finalize_cost = cost_in_microcredits(stack, function.finalize_logic().unwrap()).unwrap();
        assert_eq!(906000, finalize_cost);
    }

    #[test]
    fn test_finalize_costs_arrays() {
        let rng = &mut TestRng::default();

        // Define a program
        let program_str = r"
program test_program.aleo;
mapping storage_small:
    key as u64.public;
    value as [boolean; 8u32].public;
mapping storage_medium:
    key as u64.public;
    value as [[boolean; 8u32]; 8u32].public;
mapping storage_large:
    key as u64.public;
    value as [[[boolean; 8u32]; 8u32]; 8u32].public;
mapping storage_xlarge:
    key as u64.public;
    value as [[[[boolean; 8u32]; 8u32]; 8u32]; 8u32].public;
function store_small:
    input r0 as u64.public;
    input r1 as [boolean; 8u32].public;
    async store_small r0 r1 into r2;
    output r2 as test_program.aleo/store_small.future;
finalize store_small:
    input r0 as u64.public;
    input r1 as [boolean; 8u32].public;
    set r1 into storage_small[r0];
function store_medium:
    input r0 as u64.public;
    input r1 as [[boolean; 8u32]; 8u32].public;
    async store_medium r0 r1 into r2;
    output r2 as test_program.aleo/store_medium.future;
finalize store_medium:
    input r0 as u64.public;
    input r1 as [[boolean; 8u32]; 8u32].public;
    set r1 into storage_medium[r0];
function store_large:
    input r0 as u64.public;
    input r1 as [[[boolean; 8u32]; 8u32]; 8u32].public;
    async store_large r0 r1 into r2;
    output r2 as test_program.aleo/store_large.future;
finalize store_large:
    input r0 as u64.public;
    input r1 as [[[boolean; 8u32]; 8u32]; 8u32].public;
    set r1 into storage_large[r0];
function store_xlarge:
    input r0 as u64.public;
    input r1 as [[[[boolean; 8u32]; 8u32]; 8u32]; 8u32].public;
    async store_xlarge r0 r1 into r2;
    output r2 as test_program.aleo/store_xlarge.future;
finalize store_xlarge:
    input r0 as u64.public;
    input r1 as [[[[boolean; 8u32]; 8u32]; 8u32]; 8u32].public;
    set r1 into storage_xlarge[r0];
        ";

        // Compile the program.
        let program = Program::<CurrentNetwork>::from_str(program_str).unwrap();

        // Load the process.
        let mut process = Process::<CurrentNetwork>::load().unwrap();

        // Deploy and load the program.
        let deployment = process.deploy::<AleoV0, _>(&program, rng).unwrap();
        process.load_deployment(&deployment).unwrap();

        // Get the stack.
        let stack = process.get_stack(program.id()).unwrap();

        // Test the price of each execution.

        // Function: `store_small`
        let function = program.get_function(&Identifier::from_str("store_small").unwrap()).unwrap();
        let finalize_cost = cost_in_microcredits(stack, function.finalize_logic().unwrap()).unwrap();
        assert_eq!(16000, finalize_cost);

        // Function: `store_medium`
        let function = program.get_function(&Identifier::from_str("store_medium").unwrap()).unwrap();
        let finalize_cost = cost_in_microcredits(stack, function.finalize_logic().unwrap()).unwrap();
        assert_eq!(72000, finalize_cost);

        // Function: `store_large`
        let function = program.get_function(&Identifier::from_str("store_large").unwrap()).unwrap();
        let finalize_cost = cost_in_microcredits(stack, function.finalize_logic().unwrap()).unwrap();
        assert_eq!(520000, finalize_cost);

        // Function: `store_xlarge`
        let function = program.get_function(&Identifier::from_str("store_xlarge").unwrap()).unwrap();
        let finalize_cost = cost_in_microcredits(stack, function.finalize_logic().unwrap()).unwrap();
        assert_eq!(4104000, finalize_cost);
    }

    #[test]
    fn test_finalize_costs_big_finalize() {
        let rng = &mut TestRng::default();

        // Define a program
        let program_str = r"
program test_program.aleo;
mapping big_map:
	key as u128.public;
	value as [[[u8; 32u32]; 32u32]; 32u32].public;
function big_finalize:
    async big_finalize into r0;
    output r0 as test_program.aleo/big_finalize.future;
finalize big_finalize:
    rand.chacha into r0 as u128;
    cast  0u8 0u8 0u8 0u8 0u8 0u8 0u8 0u8 0u8 0u8 0u8 0u8 0u8 0u8 0u8 0u8 0u8 0u8 0u8 0u8 0u8 0u8 0u8 0u8 0u8 0u8 0u8 0u8 0u8 0u8 0u8 0u8 into r1 as [u8; 32u32];
    cast  r1 r1 r1 r1 r1 r1 r1 r1 r1 r1 r1 r1 r1 r1 r1 r1 r1 r1 r1 r1 r1 r1 r1 r1 r1 r1 r1 r1 r1 r1 r1 r1 into r2 as [[u8; 32u32]; 32u32];
    cast  r2 r2 r2 r2 r2 r2 r2 r2 r2 r2 r2 r2 r2 r2 r2 r2 r2 r2 r2 r2 r2 r2 r2 r2 r2 r2 r2 r2 r2 r2 r2 r2 into r3 as [[[u8; 32u32]; 32u32]; 32u32];
    add.w r0 0u128 into r4;
    set r3 into big_map[r4];
    add.w r0 1u128 into r5;
    set r3 into big_map[r5];
    add.w r0 2u128 into r6;
    set r3 into big_map[r6];
    add.w r0 3u128 into r7;
    set r3 into big_map[r7];
    add.w r0 4u128 into r8;
    set r3 into big_map[r8];
    add.w r0 5u128 into r9;
    set r3 into big_map[r9];
    add.w r0 6u128 into r10;
    set r3 into big_map[r10];
    add.w r0 7u128 into r11;
    set r3 into big_map[r11];
    add.w r0 8u128 into r12;
    set r3 into big_map[r12];
    add.w r0 9u128 into r13;
    set r3 into big_map[r13];
    add.w r0 10u128 into r14;
    set r3 into big_map[r14];
    add.w r0 11u128 into r15;
    set r3 into big_map[r15];
    add.w r0 12u128 into r16;
    set r3 into big_map[r16];
    add.w r0 13u128 into r17;
    set r3 into big_map[r17];
    add.w r0 14u128 into r18;
    set r3 into big_map[r18];
    add.w r0 15u128 into r19;
    set r3 into big_map[r19];
        ";

        // Compile the program.
        let program = Program::<CurrentNetwork>::from_str(program_str).unwrap();

        // Load the process.
        let mut process = Process::<CurrentNetwork>::load().unwrap();

        // Deploy and load the program.
        let deployment = process.deploy::<AleoV0, _>(&program, rng).unwrap();
        process.load_deployment(&deployment).unwrap();

        // Get the stack.
        let stack = process.get_stack(program.id()).unwrap();

        // Test the price of `big_finalize`.
        let function = program.get_function(&Identifier::from_str("big_finalize").unwrap()).unwrap();
        let finalize_cost = cost_in_microcredits(stack, function.finalize_logic().unwrap()).unwrap();
        assert_eq!(524_607_000, finalize_cost);
    }
}
