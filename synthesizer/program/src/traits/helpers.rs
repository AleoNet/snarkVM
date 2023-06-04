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

use console::{
    network::prelude::*,
    account::{PrivateKey},
    program::{Request, Identifier, ProgramID}
};

use parking_lot::RwLock;
use std::sync::Arc;

pub type Assignments<N> = Arc<RwLock<Vec<circuit::Assignment<<N as Environment>::Field>>>>;

#[derive(Copy, Clone, Debug)]
pub struct CallMetrics<N: Network> {
    pub program_id: ProgramID<N>,
    pub function_name: Identifier<N>,
    pub num_instructions: usize,
    pub num_request_constraints: u64,
    pub num_function_constraints: u64,
    pub num_response_constraints: u64,
}

#[derive(Clone)]
pub enum CallStack<N: Network> {
    Authorize(Vec<Request<N>>, PrivateKey<N>, Authorization<N>),
    Synthesize(Vec<Request<N>>, PrivateKey<N>, Authorization<N>),
    CheckDeployment(Vec<Request<N>>, PrivateKey<N>, Assignments<N>),
    Evaluate(Authorization<N>),
    Execute(Authorization<N>, Arc<RwLock<Trace<N>>>, Arc<RwLock<Vec<CallMetrics<N>>>>),
}

impl<N: Network> CallStack<N> {
    /// Initializes a call stack as `Self::Evaluate`.
    pub fn evaluate(authorization: Authorization<N>) -> Result<Self> {
        Ok(CallStack::Evaluate(authorization))
    }

    /// Initializes a call stack as `Self::Execute`.
    pub fn execute(
        authorization: Authorization<N>,
        trace: Arc<RwLock<Trace<N>>>,
        metrics: Arc<RwLock<Vec<CallMetrics<N>>>>,
    ) -> Result<Self> {
        Ok(CallStack::Execute(authorization, trace, metrics))
    }
}

impl<N: Network> CallStackTrait<N> for CallStack<N> {
    /// Returns a new and independent replica of the call stack.
    fn replicate(&self) -> Self {
        match self {
            CallStack::Authorize(requests, private_key, authorization) => {
                CallStack::Authorize(requests.clone(), *private_key, authorization.replicate())
            }
            CallStack::Synthesize(requests, private_key, authorization) => {
                CallStack::Synthesize(requests.clone(), *private_key, authorization.replicate())
            }
            CallStack::CheckDeployment(requests, private_key, assignments) => CallStack::CheckDeployment(
                requests.clone(),
                *private_key,
                Arc::new(RwLock::new(assignments.read().clone())),
            ),
            CallStack::Evaluate(authorization) => CallStack::Evaluate(authorization.replicate()),
            CallStack::Execute(authorization, trace, metrics) => CallStack::Execute(
                authorization.replicate(),
                Arc::new(RwLock::new(trace.read().clone())),
                Arc::new(RwLock::new(metrics.read().clone())),
            ),
        }
    }

    /// Pushes the request to the stack.
    fn push(&mut self, request: Request<N>) -> Result<()> {
        match self {
            CallStack::Authorize(requests, ..) => requests.push(request),
            CallStack::Synthesize(requests, ..) => requests.push(request),
            CallStack::CheckDeployment(requests, ..) => requests.push(request),
            CallStack::Evaluate(authorization) => authorization.push(request),
            CallStack::Execute(authorization, ..) => authorization.push(request),
        }
        Ok(())
    }

    /// Pops the request from the stack.
    fn pop(&mut self) -> Result<Request<N>> {
        match self {
            CallStack::Authorize(requests, ..)
            | CallStack::Synthesize(requests, ..)
            | CallStack::CheckDeployment(requests, ..) => {
                requests.pop().ok_or_else(|| anyhow!("No more requests on the stack"))
            }
            CallStack::Evaluate(authorization) => authorization.next(),
            CallStack::Execute(authorization, ..) => authorization.next(),
        }
    }

    /// Peeks at the next request from the stack.
    fn peek(&mut self) -> Result<Request<N>> {
        match self {
            CallStack::Authorize(requests, ..)
            | CallStack::Synthesize(requests, ..)
            | CallStack::CheckDeployment(requests, ..) => {
                requests.last().cloned().ok_or_else(|| anyhow!("No more requests on the stack"))
            }
            CallStack::Evaluate(authorization) => authorization.peek_next(),
            CallStack::Execute(authorization, ..) => authorization.peek_next(),
        }
    }
}
