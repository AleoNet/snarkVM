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

pub type Constant = Metric<usize>;
pub type Public = Metric<usize>;
pub type Private = Metric<usize>;
pub type Constraints = Metric<usize>;

/// A helper struct for tracking the number of constants, public inputs, private inputs, and constraints.
pub struct Count(pub Constant, pub Public, pub Private, pub Constraints);

impl Count {
    /// Returns a new `Count` whose constituent metrics are all `Exact`.
    pub fn exact(num_constants: usize, num_public: usize, num_private: usize, num_constraints: usize) -> Self {
        Count(
            Metric::Exact(num_constants),
            Metric::Exact(num_public),
            Metric::Exact(num_private),
            Metric::Exact(num_constraints),
        )
    }

    /// Returns a new `Count` whose constituent metrics are all exclusive `UpperBound`.
    pub fn less_than(num_constants: usize, num_public: usize, num_private: usize, num_constraints: usize) -> Self {
        CircuitMetric(
            Metric::UpperBound(Clusivity::Exclusive, num_constants),
            Metric::UpperBound(Clusivity::Exclusive, num_public),
            Metric::UpperBound(Clusivity::Exclusive, num_private),
            Metric::UpperBound(Clusivity::Exclusive, num_constraints),
        )
    }

    /// Returns a new `Count` whose constituent metrics are all inclusive `UpperBound`.
    pub fn less_than_or_equal(num_constants: usize, num_public: usize, num_private: usize, num_constraints: usize) -> Self {
        CircuitMetric(
            Metric::UpperBound(Clusivity::Inclusive, num_constants),
            Metric::UpperBound(Clusivity::Inclusive, num_public),
            Metric::UpperBound(Clusivity::Inclusive, num_private),
            Metric::UpperBound(Clusivity::Inclusive, num_constraints),
        )
    }

    /// Returns `true` if all constituent metrics are satisfied.
    pub fn is_satisfied(&self, num_constants: usize, num_public: usize, num_private: usize, num_constraints: usize) -> bool {
        self.0.is_satisfied(num_constants) &&
        self.1.is_satisfied(num_public) &&
        self.2.is_satisfied(num_private) &&
        self.3.is_satisfied(num_constraints)
    }

    /// Composes this `Count` with another `Count` by composing its constituent metrics.
    pub fn compose(&self, other: &Self) -> Self {
        CircuitMetric(
            self.0.compose(&other.0),
            self.1.compose(&other.1),
            self.2.compose(&other.2),
            self.3.compose(&other.3),
        )
    }
}


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
