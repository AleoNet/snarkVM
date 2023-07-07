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

impl<N: Network> FinalizeTypes<N> {
    /// Checks that the given operands matches the layout of the struct. The ordering of the operands matters.
    pub fn matches_struct(
        &self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        operands: &[Operand<N>],
        struct_: &Struct<N>,
    ) -> Result<()> {
        // Retrieve the struct name.
        let struct_name = struct_.name();
        // Ensure the struct name is valid.
        ensure!(!Program::is_reserved_keyword(struct_name), "Struct name '{struct_name}' is reserved");

        // Ensure the operands length is at least the minimum required.
        if operands.len() < N::MIN_STRUCT_ENTRIES {
            bail!("'{struct_name}' must have at least {} operand(s)", N::MIN_STRUCT_ENTRIES)
        }
        // Ensure the number of struct members does not exceed the maximum.
        if operands.len() > N::MAX_STRUCT_ENTRIES {
            bail!("'{struct_name}' cannot exceed {} entries", N::MAX_STRUCT_ENTRIES)
        }

        // Ensure the number of struct members match.
        let num_members = operands.len();
        let expected_num_members = struct_.members().len();
        if expected_num_members != num_members {
            bail!("'{struct_name}' expected {expected_num_members} members, found {num_members} members")
        }

        // Ensure the operand types match the struct.
        for (operand, (member_name, member_type)) in operands.iter().zip_eq(struct_.members()) {
            match operand {
                // Ensure the literal type matches the member type.
                Operand::Literal(literal) => {
                    ensure!(
                        PlaintextType::Literal(literal.to_type()) == *member_type,
                        "Struct member '{struct_name}.{member_name}' expects a {member_type}, but found '{operand}' in the operand.",
                    )
                }
                // Ensure the type of the register matches the member type.
                Operand::Register(register) => {
                    // Retrieve the type.
                    let plaintext_type = self.get_type(stack, register)?;
                    // Ensure the register type matches the member type.
                    ensure!(
                        plaintext_type == *member_type,
                        "Struct member '{struct_name}.{member_name}' expects {member_type}, but found '{plaintext_type}' in the operand '{operand}'.",
                    )
                }
                // Ensure the program ID type (address) matches the member type.
                Operand::ProgramID(..) => {
                    // Retrieve the program ID type.
                    let program_ref_type = RegisterType::Plaintext(PlaintextType::Literal(LiteralType::Address));
                    // Ensure the program ID type matches the member type.
                    ensure!(
                        program_ref_type == RegisterType::Plaintext(*member_type),
                        "Struct member '{struct_name}.{member_name}' expects {member_type}, but found '{program_ref_type}' in the operand '{operand}'.",
                    )
                }
                // If the operand is a caller, throw an error.
                Operand::Caller => bail!(
                    "Struct member '{struct_name}.{member_name}' cannot be cast from a caller in a finalize scope."
                ),
                // Ensure the block height type (u32) matches the member type.
                Operand::BlockHeight => {
                    // Retrieve the block height type.
                    let block_height_type = RegisterType::Plaintext(PlaintextType::Literal(LiteralType::U32));
                    // Ensure the block height type matches the member type.
                    ensure!(
                        block_height_type == RegisterType::Plaintext(*member_type),
                        "Struct member '{struct_name}.{member_name}' expects {member_type}, but found '{block_height_type}' in the operand '{operand}'.",
                    )
                }
            }
        }
        Ok(())
    }
}
