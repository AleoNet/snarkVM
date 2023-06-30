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

mod query;
pub use query::*;

use crate::process::{CallStack, Closure, FinalizeTypes, RegisterTypes};
use console::{
    account::Address,
    network::Network,
    prelude::Result,
    program::{Identifier, Response, Value},
    types::Field,
};

pub trait StackEvaluate<N: Network>: Clone {
    /// Evaluates a program closure on the given inputs.
    ///
    /// # Errors
    /// This method will halt if the given inputs are not the same length as the input statements.
    fn evaluate_closure<A: circuit::Aleo<Network = N>>(
        &self,
        closure: &Closure<N>,
        inputs: &[Value<N>],
        call_stack: CallStack<N>,
        caller: Address<N>,
        tvk: Field<N>,
    ) -> Result<Vec<Value<N>>>;

    /// Evaluates a program function on the given inputs.
    ///
    /// # Errors
    /// This method will halt if the given inputs are not the same length as the input statements.
    fn evaluate_function<A: circuit::Aleo<Network = N>>(&self, call_stack: CallStack<N>) -> Result<Response<N>>;
}

pub trait StackExecute<N: Network> {
    /// Executes a program closure on the given inputs.
    ///
    /// # Errors
    /// This method will halt if the given inputs are not the same length as the input statements.
    fn execute_closure<A: circuit::Aleo<Network = N>>(
        &self,
        closure: &Closure<N>,
        inputs: &[circuit::Value<A>],
        call_stack: CallStack<N>,
        caller: circuit::Address<A>,
        tvk: circuit::Field<A>,
    ) -> Result<Vec<circuit::Value<A>>>;

    /// Executes a program function on the given inputs.
    ///
    /// Note: To execute a transition, do **not** call this method. Instead, call `Process::execute`.
    ///
    /// # Errors
    /// This method will halt if the given inputs are not the same length as the input statements.
    fn execute_function<A: circuit::Aleo<Network = N>>(&self, call_stack: CallStack<N>) -> Result<Response<N>>;
}

pub trait StackProgramTypes<N: Network> {
    /// Returns the register types for the given closure or function name.
    fn get_register_types(&self, name: &Identifier<N>) -> Result<&RegisterTypes<N>>;

    /// Returns the register types for the given finalize name.
    fn get_finalize_types(&self, name: &Identifier<N>) -> Result<&FinalizeTypes<N>>;
}

pub trait RegistersCall<N: Network> {
    /// Returns the current call stack.
    fn call_stack(&self) -> CallStack<N>;
}
