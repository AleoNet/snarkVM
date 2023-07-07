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

use console::{network::prelude::*, program::Request};

use parking_lot::RwLock;
use std::{collections::VecDeque, sync::Arc};

#[derive(Clone)]
pub struct Authorization<N: Network> {
    /// The authorized requests.
    requests: Arc<RwLock<VecDeque<Request<N>>>>,
}

impl<N: Network> Authorization<N> {
    /// Initialize a new `Authorization` instance, with the given requests.
    pub fn new(requests: &[Request<N>]) -> Self {
        Self { requests: Arc::new(RwLock::new(VecDeque::from_iter(requests.iter().cloned()))) }
    }

    /// Returns a new and independent replica of the authorization.
    pub fn replicate(&self) -> Self {
        Self { requests: Arc::new(RwLock::new(self.requests.read().clone())) }
    }

    /// Returns the next `Request` in the authorization.
    pub fn peek_next(&self) -> Result<Request<N>> {
        self.requests.read().get(0).cloned().ok_or_else(|| anyhow!("Failed to peek at the next request."))
    }

    /// Returns the next `Request` from the authorization.
    pub fn next(&self) -> Result<Request<N>> {
        self.requests.write().pop_front().ok_or_else(|| anyhow!("No more requests in the authorization."))
    }

    /// Returns the `Request` at the given index.
    pub fn get(&self, index: usize) -> Result<Request<N>> {
        self.requests.read().get(index).cloned().ok_or_else(|| anyhow!("Attempted to get missing request {index}."))
    }

    /// Returns the number of `Request`s in the authorization.
    pub fn len(&self) -> usize {
        self.requests.read().len()
    }

    /// Return `true` if the authorization is empty.
    pub fn is_empty(&self) -> bool {
        self.requests.read().is_empty()
    }

    /// Appends the given `Request` to the authorization.
    pub fn push(&self, request: Request<N>) {
        self.requests.write().push_back(request);
    }

    /// Returns the requests in the authorization.
    pub fn to_vec_deque(&self) -> VecDeque<Request<N>> {
        self.requests.read().clone()
    }
}
