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

use crate::Measurement;

pub type Constant = Measurement<usize>;
pub type Public = Measurement<usize>;
pub type Private = Measurement<usize>;
pub type Constraints = Measurement<usize>;

/// A helper struct for tracking the number of constants, public inputs, private inputs, and constraints.
#[derive(Debug)]
pub struct Count(pub Constant, pub Public, pub Private, pub Constraints);

impl Count {
    /// Returns a new `Count` whose constituent metrics are all `Exact`.
    pub const fn is(num_constants: usize, num_public: usize, num_private: usize, num_constraints: usize) -> Self {
        Count(
            Measurement::Exact(num_constants),
            Measurement::Exact(num_public),
            Measurement::Exact(num_private),
            Measurement::Exact(num_constraints),
        )
    }

    /// Returns a new `Count` whose constituent metrics are all exclusive `UpperBound`.
    pub const fn less_than(
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) -> Self {
        Count(
            Measurement::UpperBound(num_constants),
            Measurement::UpperBound(num_public),
            Measurement::UpperBound(num_private),
            Measurement::UpperBound(num_constraints),
        )
    }

    /// TODO (howardwu): Deprecate this method and implement `PartialEq` & `Eq`.
    /// Returns `true` if all constituent metrics match.
    pub fn matches(&self, num_constants: usize, num_public: usize, num_private: usize, num_constraints: usize) -> bool {
        self.0.matches(num_constants)
            && self.1.matches(num_public)
            && self.2.matches(num_private)
            && self.3.matches(num_constraints)
    }

    /// TODO (howardwu): Deprecate this method and implement `Add` operation.
    /// Composes this `Count` with another `Count` by composing its constituent metrics.
    pub fn compose(&self, other: &Self) -> Self {
        Count(self.0.compose(&other.0), self.1.compose(&other.1), self.2.compose(&other.2), self.3.compose(&other.3))
    }
}
