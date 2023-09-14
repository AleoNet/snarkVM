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

use crate::CallOperator;
use console::{
    network::Network,
    prelude::{FromBytes, Parser, ToBytes},
    program::{Identifier, Register},
};

pub trait CommandTrait<N: Network>: Clone + Parser + FromBytes + ToBytes {
    type FinalizeCommand: FinalizeCommandTrait;

    /// Returns the destination registers of the command.
    fn destinations(&self) -> Vec<Register<N>>;
    /// Returns the branch target, if the command is a branch command.
    fn branch_to(&self) -> Option<&Identifier<N>>;
    /// Returns the name of the closure, finalize, or function being called, if the command is a call instruction.
    fn call_to(&self) -> Option<&CallOperator<N>>;
    /// Returns the position name, if the command is a position command.
    fn position(&self) -> Option<&Identifier<N>>;
    /// Returns `true` if the command is a closure call instruction, e.g `call.closure`.
    fn is_closure_call(&self) -> bool;
    /// Returns `true` if the command is a finalize call instruction, e.g `call.finalize`.
    fn is_finalize_call(&self) -> bool;
    /// Returns `true` if the command is a function call instruction, e.g `call.function`.
    fn is_function_call(&self) -> bool;
    /// Returns `true` if the command is a cast to record instruction.
    fn is_cast_to_record(&self) -> bool;
    /// Returns `true` if the command is a write operation.
    fn is_write(&self) -> bool;
}

pub trait FinalizeCommandTrait: Clone + PartialEq + Eq + Parser + FromBytes + ToBytes {
    /// Returns the number of operands.
    fn num_operands(&self) -> usize;
}
