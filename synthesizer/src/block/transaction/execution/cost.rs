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
    pub fn cost<C: ConsensusStorage<N>>(vm: &VM<N, C>, execution: &Self) -> Result<(u64, (u64, u64))> {
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
                Some((_, finalize)) => {
                    // Retrieve the process.
                    let process = vm.process();
                    let process_reader = process.read();

                    // Compute the cost in microcredits.
                    finalize_cost_in_microcredits(process_reader.get_stack(program.id())?, finalize)?
                }
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

/// Returns the minimum number of microcredits required to run the finalize.
pub fn finalize_cost_in_microcredits<N: Network>(stack: &Stack<N>, finalize: &Finalize<N>) -> Result<u64> {
    // Retrieve the finalize types.
    let finalize_types = stack.get_finalize_types(finalize.name())?;

    // Helper function to get the plaintext type in bytes
    fn plaintext_size_in_bytes<N: Network>(stack: &Stack<N>, plaintext_type: &PlaintextType<N>) -> Result<u64> {
        match plaintext_type {
            PlaintextType::Literal(literal_type) => {
                // Retrieve the literal size in bits.
                // TODO (raychu86): This will fail for the `Literal::Register` storing string types.
                let literal_size_in_bits = literal_type.size_in_bits::<N>()? as u64;

                // Compute the size in bytes.
                let literal_size_in_bytes = literal_size_in_bits.saturating_add(7).saturating_div(8);

                // Return the size of the literal.
                Ok(literal_size_in_bytes)
            }
            PlaintextType::Struct(struct_identifier) => {
                // Get the struct from the stack.
                let plaintext_struct = stack.program().get_struct(struct_identifier)?;

                // Get the size of the struct identifier.
                let identifier_size = plaintext_struct.name().to_bytes_le()?.len() as u64;

                // Get the size of all the members of the struct.
                let size_of_members = plaintext_struct
                    .members()
                    .iter()
                    .map(|(_, member_type)| plaintext_size_in_bytes(stack, member_type))
                    .sum::<Result<u64>>()?;

                // Return the size of the struct.
                Ok(identifier_size.saturating_add(size_of_members))
            }
        }
    }

    // Helper function to get the size of the operand type.
    let operand_size_in_bytes = |operand: &Operand<N>| {
        // Get the plaintext type from the operand.
        let plaintext_type = finalize_types.get_type_from_operand(stack, operand)?;

        // Directly return the size if the operand is a literal.
        if let (PlaintextType::Literal(literal_type), Operand::Literal(literal)) = (&plaintext_type, operand) {
            // Ensure that the literal type matches the operand type.
            ensure!(literal_type == &literal.to_type(), "Literal type mismatch.");

            Ok((literal.size_in_bits() as u64).saturating_add(7).saturating_div(8))
        } else {
            // Get the size of the operand type.
            plaintext_size_in_bytes(stack, &finalize_types.get_type_from_operand(stack, operand)?)
        }
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
        Command::Remove(_) => Ok(1000),
        Command::Set(set) => {
            // The cost in microcredits per byte of storage used by the `set` command.
            const BYTE_MULTIPLIER_SET: u64 = 1000;

            // Get the size in bytes of the key and value types.
            let key_size_in_bytes = operand_size_in_bytes(set.key())?;
            let value_size_in_bytes = operand_size_in_bytes(set.value())?;

            // Calculate the size in bytes of the key and value.
            let stored_size_in_bytes = key_size_in_bytes.saturating_add(value_size_in_bytes);

            // Calculate the cost.
            Ok(stored_size_in_bytes.saturating_mul(BYTE_MULTIPLIER_SET))
        }
        Command::BranchEq(_) | Command::BranchNeq(_) => Ok(5_000),
        Command::Position(_) => Ok(1_000),
    };
    finalize.commands().iter().map(|command| cost(command)).sum()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{vm::test_helpers::CurrentNetwork, Process, Program};
    use circuit::network::AleoV0;
    use console::program::Identifier;
    use snarkvm_utilities::TestRng;

    #[test]
    fn test_credits_finalize_costs() {
        // Get the credits.aleo program.
        let program = Program::<CurrentNetwork>::credits().unwrap();

        // Load the process.
        let process = Process::<CurrentNetwork>::load().unwrap();

        // Get the stack.
        let stack = process.get_stack(program.id()).unwrap();

        // Function: `mint`
        let function = program.get_function(&Identifier::from_str("mint").unwrap()).unwrap();
        assert!(function.finalize().is_none());

        // Function: `transfer_public`
        let function = program.get_function(&Identifier::from_str("transfer_public").unwrap()).unwrap();
        let (_, finalize) = function.finalize().unwrap();
        let finalize_cost = finalize_cost_in_microcredits(stack, finalize).unwrap();
        assert_eq!(1092000, finalize_cost);

        // Function: `transfer_private`
        let function = program.get_function(&Identifier::from_str("transfer_private").unwrap()).unwrap();
        assert!(function.finalize().is_none());

        // Function: `transfer_private_to_public`
        let function = program.get_function(&Identifier::from_str("transfer_private_to_public").unwrap()).unwrap();
        let (_, finalize) = function.finalize().unwrap();
        let finalize_cost = finalize_cost_in_microcredits(stack, finalize).unwrap();
        assert_eq!(542000, finalize_cost);

        // Function: `transfer_public_to_private`
        let function = program.get_function(&Identifier::from_str("transfer_public_to_private").unwrap()).unwrap();
        let (_, finalize) = function.finalize().unwrap();
        let finalize_cost = finalize_cost_in_microcredits(stack, finalize).unwrap();
        assert_eq!(550000, finalize_cost);

        // Function: `join`
        let function = program.get_function(&Identifier::from_str("join").unwrap()).unwrap();
        assert!(function.finalize().is_none());

        // Function: `split`
        let function = program.get_function(&Identifier::from_str("split").unwrap()).unwrap();
        assert!(function.finalize().is_none());

        // Function: `fee`
        let function = program.get_function(&Identifier::from_str("fee").unwrap()).unwrap();
        assert!(function.finalize().is_none());
    }

    #[test]
    fn test_finalize_costs() {
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
    key owner as u64.public;
    value data as small.public;

mapping storage_medium:
    key owner as u64.public;
    value data as medium.public;

mapping storage_large:
    key owner as u64.public;
    value data as large.public;

mapping storage_xlarge:
    key owner as u64.public;
    value data as xlarge.public;

function store_small:
    input r0 as u64.public;
    input r1 as small.public;
    finalize r0 r1;

finalize store_small:
    input r0 as u64.public;
    input r1 as small.public;
    set r1 into storage_small[r0];

function store_medium:
    input r0 as u64.public;
    input r1 as medium.public;
    finalize r0 r1;

finalize store_medium:
    input r0 as u64.public;
    input r1 as medium.public;
    set r1 into storage_medium[r0];

function store_large:
    input r0 as u64.public;
    input r1 as large.public;
    finalize r0 r1;

finalize store_large:
    input r0 as u64.public;
    input r1 as large.public;
    set r1 into storage_large[r0];

function store_xlarge:
    input r0 as u64.public;
    input r1 as xlarge.public;
    finalize r0 r1;

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
        let (_, finalize) = function.finalize().unwrap();
        let finalize_cost = finalize_cost_in_microcredits(stack, finalize).unwrap();
        assert_eq!(38000, finalize_cost);

        // Function: `store_medium`
        let function = program.get_function(&Identifier::from_str("store_medium").unwrap()).unwrap();
        let (_, finalize) = function.finalize().unwrap();
        let finalize_cost = finalize_cost_in_microcredits(stack, finalize).unwrap();
        assert_eq!(105000, finalize_cost);

        // Function: `store_large`
        let function = program.get_function(&Identifier::from_str("store_large").unwrap()).unwrap();
        let (_, finalize) = function.finalize().unwrap();
        let finalize_cost = finalize_cost_in_microcredits(stack, finalize).unwrap();
        assert_eq!(305000, finalize_cost);

        // Function: `store_xlarge`
        let function = program.get_function(&Identifier::from_str("store_xlarge").unwrap()).unwrap();
        let (_, finalize) = function.finalize().unwrap();
        let finalize_cost = finalize_cost_in_microcredits(stack, finalize).unwrap();
        assert_eq!(906000, finalize_cost);
    }
}
