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

// TODO: This trait is used to make explicit the operation on which a metric is defined.
//   There may be a use for this design in dispatching opcodes. If we do go down that route, do we
//   then implement Metrics on opcodes?
pub trait Operation {
    type Input;
    type Output;

    fn invoke(input: Self::Input) -> Self::Output;
}

/// Defines a metric for a given operation.
pub trait MetricForOperation: Operation {
    type Metric;

    /// Returns the metric for the given input.
    fn get_metric(input: &Self::Input) -> Self::Metric;
}
