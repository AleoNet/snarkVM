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
pub mod integers;

/// A metric is a required value that can be measured for a circuit.
#[derive(Clone, Debug)]
pub enum Metric<V: PartialOrd> {
    Equal(V),
    LowerBound(V),
    UpperBound(V),
}

impl<V: PartialOrd> Metric<V> {
    pub fn equal(value: V) -> Self {
        Metric::Equal(value)
    }

    pub fn lower_bound(value: V) -> Self {
        Metric::LowerBound(value)
    }

    pub fn upper_bound(value: V) -> Self {
        Metric::UpperBound(value)
    }

    /// Returns `true` if the value satisfies the metric.
    pub fn is_satisfied(&self, value: V) -> bool {
        match self {
            Metric::Equal(target) => value == *target,
            Metric::LowerBound(lower_bound) => value >= *lower_bound,
            Metric::UpperBound(upper_bound) => value <= *upper_bound,
        }
    }
}

/// Defines a set of metrics for a given operation.
pub trait MetricForOperation {
    type Input;
    type Metric;

    /// Returns the metric for the given input.
    fn get_metric(input: &Self::Input) -> Self::Metric;
}
