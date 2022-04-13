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

use crate::{Clusivity, Metric};

pub type Constant = Metric<usize>;
pub type Public = Metric<usize>;
pub type Private = Metric<usize>;
pub type Constraints = Metric<usize>;

/// A helper struct for tracking the number of constants, public inputs, private inputs, and constraints.
#[derive(Debug)]
pub struct CircuitCount(pub Constant, pub Public, pub Private, pub Constraints);

impl CircuitCount {
    /// Returns a new `CircuitCount` whose constituent metrics are all `Exact`.
    pub fn exact(num_constants: usize, num_public: usize, num_private: usize, num_constraints: usize) -> Self {
        CircuitCount(
            Metric::Exact(num_constants),
            Metric::Exact(num_public),
            Metric::Exact(num_private),
            Metric::Exact(num_constraints),
        )
    }

    /// Returns a new `CircuitCount` whose constituent metrics are all exclusive `UpperBound`.
    pub fn less_than(num_constants: usize, num_public: usize, num_private: usize, num_constraints: usize) -> Self {
        CircuitCount(
            Metric::UpperBound(Clusivity::Exclusive, num_constants),
            Metric::UpperBound(Clusivity::Exclusive, num_public),
            Metric::UpperBound(Clusivity::Exclusive, num_private),
            Metric::UpperBound(Clusivity::Exclusive, num_constraints),
        )
    }

    /// Returns a new `CircuitCount` whose constituent metrics are all inclusive `UpperBound`.
    pub fn less_than_or_equal(
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) -> Self {
        CircuitCount(
            Metric::UpperBound(Clusivity::Inclusive, num_constants),
            Metric::UpperBound(Clusivity::Inclusive, num_public),
            Metric::UpperBound(Clusivity::Inclusive, num_private),
            Metric::UpperBound(Clusivity::Inclusive, num_constraints),
        )
    }

    /// Returns `true` if all constituent metrics are satisfied.
    pub fn is_satisfied(
        &self,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) -> bool {
        self.0.is_satisfied(num_constants)
            && self.1.is_satisfied(num_public)
            && self.2.is_satisfied(num_private)
            && self.3.is_satisfied(num_constraints)
    }

    /// Composes this `CircuitCount` with another `CircuitCount` by composing its constituent metrics.
    pub fn compose(&self, other: &Self) -> Self {
        CircuitCount(
            self.0.compose(&other.0),
            self.1.compose(&other.1),
            self.2.compose(&other.2),
            self.3.compose(&other.3),
        )
    }
}
