// Copyright (C) 2019-2022 Aleo Systems Inc.
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

use console::{network::prelude::*, program::Request};

use parking_lot::RwLock;
use std::{collections::VecDeque, sync::Arc};

#[derive(Clone)]
pub struct Authorization<N: Network>(Arc<RwLock<VecDeque<Request<N>>>>);

impl<N: Network> Authorization<N> {
    /// Initialize a new `Authorization` instance, with the given requests.
    pub fn new(requests: &[Request<N>]) -> Self {
        Self(Arc::new(RwLock::new(VecDeque::from_iter(requests.iter().cloned()))))
    }

    /// Returns the next `Request` in the authorization.
    pub fn peek_next(&self) -> Result<Request<N>> {
        self.get(0)
    }

    /// Returns the next `Request` from the authorization.
    pub fn next(&self) -> Result<Request<N>> {
        self.0.write().pop_front().ok_or_else(|| anyhow!("No more requests in the authorization"))
    }

    /// Returns the `Request` at the given index.
    pub fn get(&self, index: usize) -> Result<Request<N>> {
        self.0.read().get(index).cloned().ok_or_else(|| anyhow!("Attempted to 'get' missing request {index}"))
    }

    /// Returns the number of `Request`s in the authorization.
    pub fn len(&self) -> usize {
        self.0.read().len()
    }

    /// Return `true` if the authorization is empty.
    pub fn is_empty(&self) -> bool {
        self.0.read().is_empty()
    }

    /// Appends the given `Request` to the authorization.
    pub fn push(&self, request: Request<N>) {
        self.0.write().push_back(request);
    }

    /// Returns the requests in the authorization.
    pub fn to_vec_deque(&self) -> VecDeque<Request<N>> {
        self.0.read().clone()
    }
}
