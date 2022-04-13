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

use std::ops::Add;

/// `Clusivity` indicates whether or not a bound is inclusive or exclusive.
#[derive(Clone, Copy, Debug)]
pub enum Clusivity {
    Inclusive,
    Exclusive,
}

impl Clusivity {
    /// Composes two variants of `Clusivity` according to the following rules.
    /// An `Exclusive` bound composed with an `Exclusive` bound, produces an `Exclusive` bound.
    /// An `Exclusive` bound composed with an `Inclusive` bound, produces an `Exclusive` bound.
    /// An `Inclusive` bound composed with an `Exclusive` bound, produces an `Exclusive` bound.
    /// An `Inclusive` bound composed with an `Inclusive` bound, produces an `Inclusive` bound.
    pub fn compose(&self, other: &Self) -> Self {
        match (self, other) {
            (Clusivity::Exclusive, Clusivity::Exclusive) => Clusivity::Exclusive,
            (Clusivity::Exclusive, Clusivity::Inclusive) => Clusivity::Exclusive,
            (Clusivity::Inclusive, Clusivity::Exclusive) => Clusivity::Exclusive,
            (Clusivity::Inclusive, Clusivity::Inclusive) => Clusivity::Inclusive,
        }
    }
}

/// A `Metric` is a quantity that can be measured.
/// The variants of the `Metric` defines a condition associated with the measurable quantity.
#[derive(Clone, Debug)]
pub enum Metric<V: Ord + Add<Output = V>> {
    Exact(V),
    Range(Clusivity, V, Clusivity, V),
    UpperBound(Clusivity, V),
}

impl<V: Ord + Add<Output = V> + Copy> Metric<V> {
    /// Returns `true` if the value satisfies the metric.
    /// For an `Exact` metric, `value` must be equal to the exact value defined by the metric.
    /// For a `Range` metric, `value` must be satisfy lower bound and the upper bound and their respective clusivities.
    /// For an `UpperBound` metric, `value` must be satisfy the upper bound and its clusivity.
    pub fn is_satisfied(&self, value: V) -> bool {
        match self {
            Metric::Exact(target) => value == *target,
            Metric::Range(lower_clusivity, lower_bound, upper_clusivity, upper_bound) => {
                match (lower_clusivity, upper_clusivity) {
                    (Clusivity::Exclusive, Clusivity::Exclusive) => value > *lower_bound && value < *upper_bound,
                    (Clusivity::Exclusive, Clusivity::Inclusive) => value > *lower_bound && value <= *upper_bound,
                    (Clusivity::Inclusive, Clusivity::Exclusive) => value >= *lower_bound && value < *upper_bound,
                    (Clusivity::Inclusive, Clusivity::Inclusive) => value >= *lower_bound && value <= *upper_bound,
                }
            }
            Metric::UpperBound(clusivity, bound) => match clusivity {
                Clusivity::Inclusive => value <= *bound,
                Clusivity::Exclusive => value < *bound,
            },
        }
    }

    /// Composes two variants of `Metric` and returns the resulting `Metric`.
    /// The composition is defined such that if a value `a` satisfies `self` and a value `b` satisfies `other`,
    /// then `a + b` satisfies the resulting `Metric`.
    pub fn compose(&self, other: &Self) -> Self {
        match (self, other) {
            // An `Exact` metric composed with an `Exact` metric, produces an `Exact` metric.
            (Metric::Exact(self_value), Metric::Exact(other_value)) => Metric::Exact(*self_value + *other_value),
            // An `Exact` metric composed with a `Range` metric, produces a `Range` metric.
            (Metric::Exact(self_value), Metric::Range(lower_clusivity, lower_bound, upper_clusivity, upper_bound)) => {
                Metric::Range(
                    *lower_clusivity,
                    *self_value + *lower_bound,
                    *upper_clusivity,
                    *self_value + *upper_bound,
                )
            }
            // An `Exact` metric composed with an `UpperBound` metric, produces an `UpperBound` metric.
            (Metric::Exact(self_value), Metric::UpperBound(clusivity, other_value)) => {
                Metric::UpperBound(*clusivity, *self_value + *other_value)
            }
            // A `Range` metric composed with an `Exact` metric, produces a `Range` metric.
            (Metric::Range(lower_clusivity, lower_bound, upper_clusivity, upper_bound), Metric::Exact(other_value)) => {
                Metric::Range(
                    *lower_clusivity,
                    *lower_bound + *other_value,
                    *upper_clusivity,
                    *upper_bound + *other_value,
                )
            }
            // A `Range` metric composed with a `Range` metric, produces a `Range` metric.
            (
                Metric::Range(self_lower_clusivity, self_lower_bound, self_upper_clusivity, self_upper_bound),
                Metric::Range(other_lower_clusivity, other_lower_bound, other_upper_clusivity, other_upper_bound),
            ) => Metric::Range(
                self_lower_clusivity.compose(other_lower_clusivity),
                *self_lower_bound + *other_lower_bound,
                self_upper_clusivity.compose(other_upper_clusivity),
                *self_upper_bound + *other_upper_bound,
            ),
            // A `Range` metric composed with an `UpperBound` metric, produces a `Range` metric.
            (
                Metric::Range(lower_clusivity, lower_bound, upper_clusivity, upper_bound),
                Metric::UpperBound(other_clusivity, other_value),
            ) => Metric::Range(
                *lower_clusivity,
                *lower_bound,
                upper_clusivity.compose(other_clusivity),
                *upper_bound + *other_value,
            ),
            // An `UpperBound` metric composed with an `UpperBound` metric, produces an `UpperBound` metric.
            (Metric::UpperBound(clusivity, self_value), Metric::Exact(other_value)) => {
                Metric::UpperBound(*clusivity, *self_value + *other_value)
            }
            // An `UpperBound` metric composed with a `Range` metric, produces an `UpperBound` metric.
            (
                Metric::UpperBound(self_clusivity, self_value),
                Metric::Range(lower_clusivity, lower_bound, upper_clusivity, upper_bound),
            ) => Metric::Range(
                *lower_clusivity,
                *lower_bound,
                self_clusivity.compose(upper_clusivity),
                *self_value + *upper_bound,
            ),
            // An `UpperBound` metric composed with an `UpperBound` metric, produces an `UpperBound` metric.
            (Metric::UpperBound(self_clusivity, self_value), Metric::UpperBound(other_clusivity, other_value)) => {
                Metric::UpperBound(self_clusivity.compose(other_clusivity), *self_value + *other_value)
            }
        }
    }
}

// TODO (@pranav) Test out metrics implementation.
