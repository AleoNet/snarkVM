// Copyright (C) 2019-2023 Aleo Systems Inc.
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

mod operation;

use crate::{instruction, Instruction, Registers, Stack};
use console::{network::prelude::*, program::RegisterType};

#[rustfmt::skip]
impl<N: Network> Stack<N> {
    /// Evaluates the instruction.
    #[inline]
    pub fn evaluate_instruction<A: circuit::Aleo<Network = N>>(
        &self,
        instruction: &Instruction<N>,
        registers: &mut Registers<N, A>,
    ) -> Result<()> {
        match instruction {
            Instruction::Abs(abs) => self.evaluate_literals(abs, registers),
            Instruction::AbsWrapped(abs_wrapped) => self.evaluate_literals(abs_wrapped, registers),
            Instruction::Add(add) => self.evaluate_literals(add, registers),
            Instruction::AddWrapped(add_wrapped) => self.evaluate_literals(add_wrapped, registers),
            Instruction::And(and) => self.evaluate_literals(and, registers),
            Instruction::AssertEq(assert_eq) => self.evaluate_assert(assert_eq, registers),
            Instruction::AssertNeq(assert_neq) => self.evaluate_assert(assert_neq, registers),
            Instruction::Call(call) => self.evaluate_call(call, registers),
            Instruction::Cast(cast) => self.evaluate_cast(cast, registers),
            Instruction::CommitBHP256(commit_bhp256) => self.evaluate_commit(commit_bhp256, registers),
            Instruction::CommitBHP512(commit_bhp512) => self.evaluate_commit(commit_bhp512, registers),
            Instruction::CommitBHP768(commit_bhp768) => self.evaluate_commit(commit_bhp768, registers),
            Instruction::CommitBHP1024(commit_bhp1024) => self.evaluate_commit(commit_bhp1024, registers),
            Instruction::CommitPED64(commit_ped64) => self.evaluate_commit(commit_ped64, registers),
            Instruction::CommitPED128(commit_ped128) => self.evaluate_commit(commit_ped128, registers),
            Instruction::Div(div) => self.evaluate_literals(div, registers),
            Instruction::DivWrapped(div_wrapped) => self.evaluate_literals(div_wrapped, registers),
            Instruction::Double(double) => self.evaluate_literals(double, registers),
            Instruction::GreaterThan(greater_than) => self.evaluate_literals(greater_than, registers),
            Instruction::GreaterThanOrEqual(greater_than_or_equal) => self.evaluate_literals(greater_than_or_equal, registers),
            Instruction::HashBHP256(hash_bhp256) => self.evaluate_hash(hash_bhp256, registers),
            Instruction::HashBHP512(hash_bhp512) => self.evaluate_hash(hash_bhp512, registers),
            Instruction::HashBHP768(hash_bhp768) => self.evaluate_hash(hash_bhp768, registers),
            Instruction::HashBHP1024(hash_bhp1024) => self.evaluate_hash(hash_bhp1024, registers),
            Instruction::HashPED64(hash_ped64) => self.evaluate_hash(hash_ped64, registers),
            Instruction::HashPED128(hash_ped128) => self.evaluate_hash(hash_ped128, registers),
            Instruction::HashPSD2(hash_psd2) => self.evaluate_hash(hash_psd2, registers),
            Instruction::HashPSD4(hash_psd4) => self.evaluate_hash(hash_psd4, registers),
            Instruction::HashPSD8(hash_psd8) => self.evaluate_hash(hash_psd8, registers),
            Instruction::Inv(inv) => self.evaluate_literals(inv, registers),
            Instruction::IsEq(is_eq) => self.evaluate_is(is_eq, registers),
            Instruction::IsNeq(is_neq) => self.evaluate_is(is_neq, registers),
            Instruction::LessThan(less_than) => self.evaluate_literals(less_than, registers),
            Instruction::LessThanOrEqual(less_than_or_equal) => self.evaluate_literals(less_than_or_equal, registers),
            Instruction::Modulo(modulo) => self.evaluate_literals(modulo, registers),
            Instruction::Mul(mul) => self.evaluate_literals(mul, registers),
            Instruction::MulWrapped(mul_wrapped) => self.evaluate_literals(mul_wrapped, registers),
            Instruction::Nand(nand) => self.evaluate_literals(nand, registers),
            Instruction::Neg(neg) => self.evaluate_literals(neg, registers),
            Instruction::Nor(nor) => self.evaluate_literals(nor, registers),
            Instruction::Not(not) => self.evaluate_literals(not, registers),
            Instruction::Or(or) => self.evaluate_literals(or, registers),
            Instruction::Pow(pow) => self.evaluate_literals(pow, registers),
            Instruction::PowWrapped(pow_wrapped) => self.evaluate_literals(pow_wrapped, registers),
            Instruction::Rem(rem) => self.evaluate_literals(rem, registers),
            Instruction::RemWrapped(rem_wrapped) => self.evaluate_literals(rem_wrapped, registers),
            Instruction::Shl(shl) => self.evaluate_literals(shl, registers),
            Instruction::ShlWrapped(shl_wrapped) => self.evaluate_literals(shl_wrapped, registers),
            Instruction::Shr(shr) => self.evaluate_literals(shr, registers),
            Instruction::ShrWrapped(shr_wrapped) => self.evaluate_literals(shr_wrapped, registers),
            Instruction::Square(square) => self.evaluate_literals(square, registers),
            Instruction::SquareRoot(square_root) => self.evaluate_literals(square_root, registers),
            Instruction::Sub(sub) => self.evaluate_literals(sub, registers),
            Instruction::SubWrapped(sub_wrapped) => self.evaluate_literals(sub_wrapped, registers),
            Instruction::Ternary(ternary) => self.evaluate_literals(ternary, registers),
            Instruction::Xor(xor) => self.evaluate_literals(xor, registers),
        }
    }

    /// Executes the instruction.
    #[inline]
    #[rustfmt::skip]
    pub fn execute_instruction<A: circuit::Aleo<Network = N>>(
        &self,
        instruction: &Instruction<N>,
        registers: &mut Registers<N, A>,
    ) -> Result<()> {
        match instruction {
            Instruction::Abs(abs) => self.execute_literals(abs, registers),
            Instruction::AbsWrapped(abs_wrapped) => self.execute_literals(abs_wrapped, registers),
            Instruction::Add(add) => self.execute_literals(add, registers),
            Instruction::AddWrapped(add_wrapped) => self.execute_literals(add_wrapped, registers),
            Instruction::And(and) => self.execute_literals(and, registers),
            Instruction::AssertEq(assert_eq) => self.execute_assert(assert_eq, registers),
            Instruction::AssertNeq(assert_neq) => self.execute_assert(assert_neq, registers),
            Instruction::Call(call) => self.execute_call(call, registers),
            Instruction::Cast(cast) => self.execute_cast(cast, registers),
            Instruction::CommitBHP256(commit_bhp256) => self.execute_commit(commit_bhp256, registers),
            Instruction::CommitBHP512(commit_bhp512) => self.execute_commit(commit_bhp512, registers),
            Instruction::CommitBHP768(commit_bhp768) => self.execute_commit(commit_bhp768, registers),
            Instruction::CommitBHP1024(commit_bhp1024) => self.execute_commit(commit_bhp1024, registers),
            Instruction::CommitPED64(commit_ped64) => self.execute_commit(commit_ped64, registers),
            Instruction::CommitPED128(commit_ped128) => self.execute_commit(commit_ped128, registers),
            Instruction::Div(div) => self.execute_literals(div, registers),
            Instruction::DivWrapped(div_wrapped) => self.execute_literals(div_wrapped, registers),
            Instruction::Double(double) => self.execute_literals(double, registers),
            Instruction::GreaterThan(greater_than) => self.execute_literals(greater_than, registers),
            Instruction::GreaterThanOrEqual(greater_than_or_equal) => self.execute_literals(greater_than_or_equal, registers),
            Instruction::HashBHP256(hash_bhp256) => self.execute_hash(hash_bhp256, registers),
            Instruction::HashBHP512(hash_bhp512) => self.execute_hash(hash_bhp512, registers),
            Instruction::HashBHP768(hash_bhp768) => self.execute_hash(hash_bhp768, registers),
            Instruction::HashBHP1024(hash_bhp1024) => self.execute_hash(hash_bhp1024, registers),
            Instruction::HashPED64(hash_ped64) => self.execute_hash(hash_ped64, registers),
            Instruction::HashPED128(hash_ped128) => self.execute_hash(hash_ped128, registers),
            Instruction::HashPSD2(hash_psd2) => self.execute_hash(hash_psd2, registers),
            Instruction::HashPSD4(hash_psd4) => self.execute_hash(hash_psd4, registers),
            Instruction::HashPSD8(hash_psd8) => self.execute_hash(hash_psd8, registers),
            Instruction::Inv(inv) => self.execute_literals(inv, registers),
            Instruction::IsEq(is_eq) => self.execute_is(is_eq, registers),
            Instruction::IsNeq(is_neq) => self.execute_is(is_neq, registers),
            Instruction::LessThan(less_than) => self.execute_literals(less_than, registers),
            Instruction::LessThanOrEqual(less_than_or_equal) => self.execute_literals(less_than_or_equal, registers),
            Instruction::Modulo(modulo) => self.execute_literals(modulo, registers),
            Instruction::Mul(mul) => self.execute_literals(mul, registers),
            Instruction::MulWrapped(mul_wrapped) => self.execute_literals(mul_wrapped, registers),
            Instruction::Nand(nand) => self.execute_literals(nand, registers),
            Instruction::Neg(neg) => self.execute_literals(neg, registers),
            Instruction::Nor(nor) => self.execute_literals(nor, registers),
            Instruction::Not(not) => self.execute_literals(not, registers),
            Instruction::Or(or) => self.execute_literals(or, registers),
            Instruction::Pow(pow) => self.execute_literals(pow, registers),
            Instruction::PowWrapped(pow_wrapped) => self.execute_literals(pow_wrapped, registers),
            Instruction::Rem(rem) => self.execute_literals(rem, registers),
            Instruction::RemWrapped(rem_wrapped) => self.execute_literals(rem_wrapped, registers),
            Instruction::Shl(shl) => self.execute_literals(shl, registers),
            Instruction::ShlWrapped(shl_wrapped) => self.execute_literals(shl_wrapped, registers),
            Instruction::Shr(shr) => self.execute_literals(shr, registers),
            Instruction::ShrWrapped(shr_wrapped) => self.execute_literals(shr_wrapped, registers),
            Instruction::Square(square) => self.execute_literals(square, registers),
            Instruction::SquareRoot(square_root) => self.execute_literals(square_root, registers),
            Instruction::Sub(sub) => self.execute_literals(sub, registers),
            Instruction::SubWrapped(sub_wrapped) => self.execute_literals(sub_wrapped, registers),
            Instruction::Ternary(ternary) => self.execute_literals(ternary, registers),
            Instruction::Xor(xor) => self.execute_literals(xor, registers),
        }
    }

    /// Returns the output type from the given input types.
    #[inline]
    pub fn instruction_output_types(
        &self,
        instruction: &Instruction<N>,
        input_types: &[RegisterType<N>],
    ) -> Result<Vec<RegisterType<N>>> {
        match instruction {
            Instruction::Abs(abs) => self.literals_output_types(abs, input_types),
            Instruction::AbsWrapped(abs_wrapped) => self.literals_output_types(abs_wrapped, input_types),
            Instruction::Add(add) => self.literals_output_types(add, input_types),
            Instruction::AddWrapped(add_wrapped) => self.literals_output_types(add_wrapped, input_types),
            Instruction::And(and) => self.literals_output_types(and, input_types),
            Instruction::AssertEq(assert_eq) => self.assert_output_types(assert_eq, input_types),
            Instruction::AssertNeq(assert_neq) => self.assert_output_types(assert_neq, input_types),
            Instruction::Call(call) => self.call_output_types(call, input_types),
            Instruction::Cast(cast) => self.cast_output_types(cast, input_types),
            Instruction::CommitBHP256(commit_bhp256) => self.commit_output_types(commit_bhp256, input_types),
            Instruction::CommitBHP512(commit_bhp512) => self.commit_output_types(commit_bhp512, input_types),
            Instruction::CommitBHP768(commit_bhp768) => self.commit_output_types(commit_bhp768, input_types),
            Instruction::CommitBHP1024(commit_bhp1024) => self.commit_output_types(commit_bhp1024, input_types),
            Instruction::CommitPED64(commit_ped64) => self.commit_output_types(commit_ped64, input_types),
            Instruction::CommitPED128(commit_ped128) => self.commit_output_types(commit_ped128, input_types),
            Instruction::Div(div) => self.literals_output_types(div, input_types),
            Instruction::DivWrapped(div_wrapped) => self.literals_output_types(div_wrapped, input_types),
            Instruction::Double(double) => self.literals_output_types(double, input_types),
            Instruction::GreaterThan(greater_than) => self.literals_output_types(greater_than, input_types),
            Instruction::GreaterThanOrEqual(greater_than_or_equal) => self.literals_output_types(greater_than_or_equal, input_types),
            Instruction::HashBHP256(hash_bhp256) => self.hash_output_types(hash_bhp256, input_types),
            Instruction::HashBHP512(hash_bhp512) => self.hash_output_types(hash_bhp512, input_types),
            Instruction::HashBHP768(hash_bhp768) => self.hash_output_types(hash_bhp768, input_types),
            Instruction::HashBHP1024(hash_bhp1024) => self.hash_output_types(hash_bhp1024, input_types),
            Instruction::HashPED64(hash_ped64) => self.hash_output_types(hash_ped64, input_types),
            Instruction::HashPED128(hash_ped128) => self.hash_output_types(hash_ped128, input_types),
            Instruction::HashPSD2(hash_psd2) => self.hash_output_types(hash_psd2, input_types),
            Instruction::HashPSD4(hash_psd4) => self.hash_output_types(hash_psd4, input_types),
            Instruction::HashPSD8(hash_psd8) => self.hash_output_types(hash_psd8, input_types),
            Instruction::Inv(inv) => self.literals_output_types(inv, input_types),
            Instruction::IsEq(is_eq) => self.is_output_types(is_eq, input_types),
            Instruction::IsNeq(is_neq) => self.is_output_types(is_neq, input_types),
            Instruction::LessThan(less_than) => self.literals_output_types(less_than, input_types),
            Instruction::LessThanOrEqual(less_than_or_equal) => self.literals_output_types(less_than_or_equal, input_types),
            Instruction::Modulo(modulo) => self.literals_output_types(modulo, input_types),
            Instruction::Mul(mul) => self.literals_output_types(mul, input_types),
            Instruction::MulWrapped(mul_wrapped) => self.literals_output_types(mul_wrapped, input_types),
            Instruction::Nand(nand) => self.literals_output_types(nand, input_types),
            Instruction::Neg(neg) => self.literals_output_types(neg, input_types),
            Instruction::Nor(nor) => self.literals_output_types(nor, input_types),
            Instruction::Not(not) => self.literals_output_types(not, input_types),
            Instruction::Or(or) => self.literals_output_types(or, input_types),
            Instruction::Pow(pow) => self.literals_output_types(pow, input_types),
            Instruction::PowWrapped(pow_wrapped) => self.literals_output_types(pow_wrapped, input_types),
            Instruction::Rem(rem) => self.literals_output_types(rem, input_types),
            Instruction::RemWrapped(rem_wrapped) => self.literals_output_types(rem_wrapped, input_types),
            Instruction::Shl(shl) => self.literals_output_types(shl, input_types),
            Instruction::ShlWrapped(shl_wrapped) => self.literals_output_types(shl_wrapped, input_types),
            Instruction::Shr(shr) => self.literals_output_types(shr, input_types),
            Instruction::ShrWrapped(shr_wrapped) => self.literals_output_types(shr_wrapped, input_types),
            Instruction::Square(square) => self.literals_output_types(square, input_types),
            Instruction::SquareRoot(square_root) => self.literals_output_types(square_root, input_types),
            Instruction::Sub(sub) => self.literals_output_types(sub, input_types),
            Instruction::SubWrapped(sub_wrapped) => self.literals_output_types(sub_wrapped, input_types),
            Instruction::Ternary(ternary) => self.literals_output_types(ternary, input_types),
            Instruction::Xor(xor) => self.literals_output_types(xor, input_types),
        }
    }
}
