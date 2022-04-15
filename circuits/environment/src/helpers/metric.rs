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

#[cfg(test)]
mod test {
    use super::*;
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: usize = 1024;

    #[test]
    fn test_exact_is_satisfied() {
        for _ in 0..ITERATIONS {
            // Generate a random `Metric` and candidate value.
            let value: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;
            let metric = Metric::Exact(value);

            // Check that the metric is only satisfied if the candidate is equal to the value.
            assert!(metric.is_satisfied(value));
            if candidate == value {
                assert!(metric.is_satisfied(candidate));
            } else {
                assert!(!metric.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_exclusive_exclusive_range_is_satisfied() {
        for _ in 0..ITERATIONS {
            // Generate a random `Metric::UpperBound` and candidate value.
            let first_bound: usize = u16::rand(&mut test_rng()) as usize;
            let second_bound: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;
            let (metric, lower_bound, upper_bound) = if first_bound <= second_bound {
                (
                    Metric::Range(Clusivity::Exclusive, first_bound, Clusivity::Exclusive, second_bound),
                    first_bound,
                    second_bound,
                )
            } else {
                (
                    Metric::Range(Clusivity::Exclusive, second_bound, Clusivity::Exclusive, first_bound),
                    second_bound,
                    first_bound,
                )
            };

            // Check that the metric is only satisfied if the candidate is less than upper_bound.
            assert!(!metric.is_satisfied(lower_bound));
            assert!(!metric.is_satisfied(upper_bound));
            if lower_bound < candidate && candidate < upper_bound {
                assert!(metric.is_satisfied(candidate));
            } else {
                assert!(!metric.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_exclusive_inclusive_range_is_satisfied() {
        for _ in 0..ITERATIONS {
            // Generate a random `Metric::UpperBound` and candidate value.
            let first_bound: usize = u16::rand(&mut test_rng()) as usize;
            let second_bound: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;
            let (metric, lower_bound, upper_bound) = if first_bound <= second_bound {
                (
                    Metric::Range(Clusivity::Exclusive, first_bound, Clusivity::Inclusive, second_bound),
                    first_bound,
                    second_bound,
                )
            } else {
                (
                    Metric::Range(Clusivity::Exclusive, second_bound, Clusivity::Inclusive, first_bound),
                    second_bound,
                    first_bound,
                )
            };

            // Check that the metric is only satisfied if the candidate is less than upper_bound.
            assert!(!metric.is_satisfied(lower_bound));
            assert!(metric.is_satisfied(upper_bound));
            if lower_bound < candidate && candidate <= upper_bound {
                assert!(metric.is_satisfied(candidate));
            } else {
                assert!(!metric.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_inclusive_exclusive_range_is_satisfied() {
        for _ in 0..ITERATIONS {
            // Generate a random `Metric::UpperBound` and candidate value.
            let first_bound: usize = u16::rand(&mut test_rng()) as usize;
            let second_bound: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;
            let (metric, lower_bound, upper_bound) = if first_bound <= second_bound {
                (
                    Metric::Range(Clusivity::Inclusive, first_bound, Clusivity::Exclusive, second_bound),
                    first_bound,
                    second_bound,
                )
            } else {
                (
                    Metric::Range(Clusivity::Inclusive, second_bound, Clusivity::Exclusive, first_bound),
                    second_bound,
                    first_bound,
                )
            };

            // Check that the metric is only satisfied if the candidate is less than upper_bound.
            assert!(metric.is_satisfied(lower_bound));
            assert!(!metric.is_satisfied(upper_bound));
            if lower_bound <= candidate && candidate < upper_bound {
                assert!(metric.is_satisfied(candidate));
            } else {
                assert!(!metric.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_inclusive_inclusive_range_is_satisfied() {
        for _ in 0..ITERATIONS {
            // Generate a random `Metric::UpperBound` and candidate value.
            let first_bound: usize = u16::rand(&mut test_rng()) as usize;
            let second_bound: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;
            let (metric, lower_bound, upper_bound) = if first_bound <= second_bound {
                (
                    Metric::Range(Clusivity::Inclusive, first_bound, Clusivity::Inclusive, second_bound),
                    first_bound,
                    second_bound,
                )
            } else {
                (
                    Metric::Range(Clusivity::Inclusive, second_bound, Clusivity::Inclusive, first_bound),
                    second_bound,
                    first_bound,
                )
            };

            // Check that the metric is only satisfied if the candidate is less than upper_bound.
            assert!(metric.is_satisfied(lower_bound));
            assert!(metric.is_satisfied(upper_bound));
            if lower_bound <= candidate && candidate <= upper_bound {
                assert!(metric.is_satisfied(candidate));
            } else {
                assert!(!metric.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_exclusive_upper_bound_is_satisfied() {
        for _ in 0..ITERATIONS {
            // Generate a random `Metric::UpperBound` and candidate value.
            let upper_bound: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;
            let metric = Metric::UpperBound(Clusivity::Exclusive, upper_bound);

            // Check that the metric is only satisfied if the candidate is less than upper_bound.
            assert!(!metric.is_satisfied(upper_bound));
            if candidate < upper_bound {
                assert!(metric.is_satisfied(candidate));
            } else {
                assert!(!metric.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_inclusive_upper_bound_is_satisfied() {
        for _ in 0..ITERATIONS {
            // Generate a random `Metric::UpperBound` and candidate value.
            let upper_bound: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;
            let metric = Metric::UpperBound(Clusivity::Inclusive, upper_bound);

            // Check that the metric is only satisfied if the candidate is less than or equal to upper_bound.
            assert!(metric.is_satisfied(upper_bound));
            if candidate <= upper_bound {
                assert!(metric.is_satisfied(candidate));
            } else {
                assert!(!metric.is_satisfied(candidate));
            }
        }
    }

    // Test composition of metrics.

    #[test]
    fn test_exact_compose_with_exact() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let a = Metric::Exact(first);
            let b = Metric::Exact(second);
            let c = a.compose(&b);

            assert!(c.is_satisfied(first + second));
            if candidate == first + second {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_exact_compose_with_exclusive_exclusive_range() {
        let value: usize = u16::rand(&mut test_rng()) as usize;
        let first_bound: usize = u16::rand(&mut test_rng()) as usize;
        let second_bound: usize = u16::rand(&mut test_rng()) as usize;
        let candidate: usize = u16::rand(&mut test_rng()) as usize;

        let a = Metric::Exact(value);
        let (b, lower_bound, upper_bound) = if first_bound <= second_bound {
            (
                Metric::Range(Clusivity::Exclusive, first_bound, Clusivity::Exclusive, second_bound),
                first_bound,
                second_bound,
            )
        } else {
            (
                Metric::Range(Clusivity::Exclusive, second_bound, Clusivity::Exclusive, first_bound),
                second_bound,
                first_bound,
            )
        };
        let c = a.compose(&b);

        assert!(!c.is_satisfied(value + lower_bound));
        assert!(!c.is_satisfied(value + upper_bound));
        if value + lower_bound < candidate && candidate < value + upper_bound {
            assert!(c.is_satisfied(candidate));
        } else {
            assert!(!c.is_satisfied(candidate));
        }
    }

    #[test]
    fn test_exact_compose_with_exclusive_inclusive_range() {
        let value: usize = u16::rand(&mut test_rng()) as usize;
        let first_bound: usize = u16::rand(&mut test_rng()) as usize;
        let second_bound: usize = u16::rand(&mut test_rng()) as usize;
        let candidate: usize = u16::rand(&mut test_rng()) as usize;

        let a = Metric::Exact(value);
        let (b, lower_bound, upper_bound) = if first_bound <= second_bound {
            (
                Metric::Range(Clusivity::Exclusive, first_bound, Clusivity::Inclusive, second_bound),
                first_bound,
                second_bound,
            )
        } else {
            (
                Metric::Range(Clusivity::Exclusive, second_bound, Clusivity::Inclusive, first_bound),
                second_bound,
                first_bound,
            )
        };
        let c = a.compose(&b);

        assert!(!c.is_satisfied(value + lower_bound));
        assert!(c.is_satisfied(value + upper_bound));
        if value + lower_bound < candidate && candidate <= value + upper_bound {
            assert!(c.is_satisfied(candidate));
        } else {
            assert!(!c.is_satisfied(candidate));
        }
    }

    #[test]
    fn test_exact_compose_with_inclusive_exclusive_range() {
        let value: usize = u16::rand(&mut test_rng()) as usize;
        let first_bound: usize = u16::rand(&mut test_rng()) as usize;
        let second_bound: usize = u16::rand(&mut test_rng()) as usize;
        let candidate: usize = u16::rand(&mut test_rng()) as usize;

        let a = Metric::Exact(value);
        let (b, lower_bound, upper_bound) = if first_bound <= second_bound {
            (
                Metric::Range(Clusivity::Inclusive, first_bound, Clusivity::Exclusive, second_bound),
                first_bound,
                second_bound,
            )
        } else {
            (
                Metric::Range(Clusivity::Inclusive, second_bound, Clusivity::Exclusive, first_bound),
                second_bound,
                first_bound,
            )
        };
        let c = a.compose(&b);

        assert!(c.is_satisfied(value + lower_bound));
        assert!(!c.is_satisfied(value + upper_bound));
        if value + lower_bound <= candidate && candidate < value + upper_bound {
            assert!(c.is_satisfied(candidate));
        } else {
            assert!(!c.is_satisfied(candidate));
        }
    }

    #[test]
    fn test_exact_compose_with_inclusive_inclusive_range() {
        let value: usize = u16::rand(&mut test_rng()) as usize;
        let first_bound: usize = u16::rand(&mut test_rng()) as usize;
        let second_bound: usize = u16::rand(&mut test_rng()) as usize;
        let candidate: usize = u16::rand(&mut test_rng()) as usize;

        let a = Metric::Exact(value);
        let (b, lower_bound, upper_bound) = if first_bound <= second_bound {
            (
                Metric::Range(Clusivity::Inclusive, first_bound, Clusivity::Inclusive, second_bound),
                first_bound,
                second_bound,
            )
        } else {
            (
                Metric::Range(Clusivity::Inclusive, second_bound, Clusivity::Inclusive, first_bound),
                second_bound,
                first_bound,
            )
        };
        let c = a.compose(&b);

        assert!(c.is_satisfied(value + lower_bound));
        assert!(c.is_satisfied(value + upper_bound));
        if value + lower_bound <= candidate && candidate <= value + upper_bound {
            assert!(c.is_satisfied(candidate));
        } else {
            assert!(!c.is_satisfied(candidate));
        }
    }

    #[test]
    fn test_exact_compose_with_exclusive_upper_bound() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let a = Metric::Exact(first);
            let b = Metric::UpperBound(Clusivity::Exclusive, second);
            let c = a.compose(&b);

            assert!(!c.is_satisfied(first + second));
            if candidate < first + second {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_exact_compose_with_inclusive_upper_bound() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let a = Metric::Exact(first);
            let b = Metric::UpperBound(Clusivity::Inclusive, second);
            let c = a.compose(&b);

            assert!(c.is_satisfied(first + second));
            if candidate <= first + second {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_exclusive_exclusive_range_compose_with_exact() {
        let value: usize = u16::rand(&mut test_rng()) as usize;
        let first_bound: usize = u16::rand(&mut test_rng()) as usize;
        let second_bound: usize = u16::rand(&mut test_rng()) as usize;
        let candidate: usize = u16::rand(&mut test_rng()) as usize;

        let (a, lower_bound, upper_bound) = if first_bound <= second_bound {
            (
                Metric::Range(Clusivity::Exclusive, first_bound, Clusivity::Exclusive, second_bound),
                first_bound,
                second_bound,
            )
        } else {
            (
                Metric::Range(Clusivity::Exclusive, second_bound, Clusivity::Exclusive, first_bound),
                second_bound,
                first_bound,
            )
        };
        let b = Metric::Exact(value);
        let c = a.compose(&b);

        assert!(!c.is_satisfied(value + lower_bound));
        assert!(!c.is_satisfied(value + upper_bound));
        if value + lower_bound < candidate && candidate < value + upper_bound {
            assert!(c.is_satisfied(candidate));
        } else {
            assert!(!c.is_satisfied(candidate));
        }
    }

    #[test]
    fn test_exclusive_inclusive_range_compose_with_exact() {
        let value: usize = u16::rand(&mut test_rng()) as usize;
        let first_bound: usize = u16::rand(&mut test_rng()) as usize;
        let second_bound: usize = u16::rand(&mut test_rng()) as usize;
        let candidate: usize = u16::rand(&mut test_rng()) as usize;

        let (a, lower_bound, upper_bound) = if first_bound <= second_bound {
            (
                Metric::Range(Clusivity::Exclusive, first_bound, Clusivity::Inclusive, second_bound),
                first_bound,
                second_bound,
            )
        } else {
            (
                Metric::Range(Clusivity::Exclusive, second_bound, Clusivity::Inclusive, first_bound),
                second_bound,
                first_bound,
            )
        };
        let b = Metric::Exact(value);
        let c = a.compose(&b);

        assert!(!c.is_satisfied(value + lower_bound));
        assert!(c.is_satisfied(value + upper_bound));
        if value + lower_bound < candidate && candidate <= value + upper_bound {
            assert!(c.is_satisfied(candidate));
        } else {
            assert!(!c.is_satisfied(candidate));
        }
    }

    #[test]
    fn test_inclusive_exclusive_range_compose_with_exact() {
        let value: usize = u16::rand(&mut test_rng()) as usize;
        let first_bound: usize = u16::rand(&mut test_rng()) as usize;
        let second_bound: usize = u16::rand(&mut test_rng()) as usize;
        let candidate: usize = u16::rand(&mut test_rng()) as usize;

        let (a, lower_bound, upper_bound) = if first_bound <= second_bound {
            (
                Metric::Range(Clusivity::Inclusive, first_bound, Clusivity::Exclusive, second_bound),
                first_bound,
                second_bound,
            )
        } else {
            (
                Metric::Range(Clusivity::Inclusive, second_bound, Clusivity::Exclusive, first_bound),
                second_bound,
                first_bound,
            )
        };
        let b = Metric::Exact(value);
        let c = a.compose(&b);

        assert!(c.is_satisfied(value + lower_bound));
        assert!(!c.is_satisfied(value + upper_bound));
        if value + lower_bound <= candidate && candidate < value + upper_bound {
            assert!(c.is_satisfied(candidate));
        } else {
            assert!(!c.is_satisfied(candidate));
        }
    }

    #[test]
    fn test_inclusive_inclusive_range_compose_with_exact() {
        let value: usize = u16::rand(&mut test_rng()) as usize;
        let first_bound: usize = u16::rand(&mut test_rng()) as usize;
        let second_bound: usize = u16::rand(&mut test_rng()) as usize;
        let candidate: usize = u16::rand(&mut test_rng()) as usize;

        let (a, lower_bound, upper_bound) = if first_bound <= second_bound {
            (
                Metric::Range(Clusivity::Inclusive, first_bound, Clusivity::Inclusive, second_bound),
                first_bound,
                second_bound,
            )
        } else {
            (
                Metric::Range(Clusivity::Inclusive, second_bound, Clusivity::Inclusive, first_bound),
                second_bound,
                first_bound,
            )
        };
        let b = Metric::Exact(value);
        let c = a.compose(&b);

        assert!(c.is_satisfied(value + lower_bound));
        assert!(c.is_satisfied(value + upper_bound));
        if value + lower_bound <= candidate && candidate <= value + upper_bound {
            assert!(c.is_satisfied(candidate));
        } else {
            assert!(!c.is_satisfied(candidate));
        }
    }

    #[test]
    fn test_exclusive_exclusive_range_compose_with_exclusive_exclusive_range() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let third: usize = u16::rand(&mut test_rng()) as usize;
            let fourth: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let (a, first_lower_bound, first_upper_bound) = if first <= second {
                (Metric::Range(Clusivity::Exclusive, first, Clusivity::Exclusive, second), first, second)
            } else {
                (Metric::Range(Clusivity::Exclusive, second, Clusivity::Exclusive, first), second, first)
            };
            let (b, second_lower_bound, second_upper_bound) = if third <= fourth {
                (Metric::Range(Clusivity::Exclusive, third, Clusivity::Exclusive, fourth), third, fourth)
            } else {
                (Metric::Range(Clusivity::Exclusive, fourth, Clusivity::Exclusive, third), fourth, third)
            };
            let c = a.compose(&b);

            assert!(!c.is_satisfied(first_lower_bound + second_lower_bound));
            assert!(!c.is_satisfied(first_upper_bound + second_upper_bound));
            if first_lower_bound + second_lower_bound < candidate && candidate < first_upper_bound + second_upper_bound
            {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_exclusive_exclusive_range_compose_with_exclusive_inclusive_range() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let third: usize = u16::rand(&mut test_rng()) as usize;
            let fourth: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let (a, first_lower_bound, first_upper_bound) = if first <= second {
                (Metric::Range(Clusivity::Exclusive, first, Clusivity::Exclusive, second), first, second)
            } else {
                (Metric::Range(Clusivity::Exclusive, second, Clusivity::Exclusive, first), second, first)
            };
            let (b, second_lower_bound, second_upper_bound) = if third <= fourth {
                (Metric::Range(Clusivity::Exclusive, third, Clusivity::Inclusive, fourth), third, fourth)
            } else {
                (Metric::Range(Clusivity::Exclusive, fourth, Clusivity::Inclusive, third), fourth, third)
            };
            let c = a.compose(&b);

            assert!(!c.is_satisfied(first_lower_bound + second_lower_bound));
            assert!(!c.is_satisfied(first_upper_bound + second_upper_bound));
            if first_lower_bound + second_lower_bound < candidate && candidate < first_upper_bound + second_upper_bound
            {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_exclusive_exclusive_range_compose_with_inclusive_exclusive_range() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let third: usize = u16::rand(&mut test_rng()) as usize;
            let fourth: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let (a, first_lower_bound, first_upper_bound) = if first <= second {
                (Metric::Range(Clusivity::Exclusive, first, Clusivity::Exclusive, second), first, second)
            } else {
                (Metric::Range(Clusivity::Exclusive, second, Clusivity::Exclusive, first), second, first)
            };
            let (b, second_lower_bound, second_upper_bound) = if third <= fourth {
                (Metric::Range(Clusivity::Inclusive, third, Clusivity::Exclusive, fourth), third, fourth)
            } else {
                (Metric::Range(Clusivity::Inclusive, fourth, Clusivity::Exclusive, third), fourth, third)
            };
            let c = a.compose(&b);

            assert!(!c.is_satisfied(first_lower_bound + second_lower_bound));
            assert!(!c.is_satisfied(first_upper_bound + second_upper_bound));
            if first_lower_bound + second_lower_bound < candidate && candidate < first_upper_bound + second_upper_bound
            {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_exclusive_exclusive_range_compose_with_inclusive_inclusive_range() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let third: usize = u16::rand(&mut test_rng()) as usize;
            let fourth: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let (a, first_lower_bound, first_upper_bound) = if first <= second {
                (Metric::Range(Clusivity::Exclusive, first, Clusivity::Exclusive, second), first, second)
            } else {
                (Metric::Range(Clusivity::Exclusive, second, Clusivity::Exclusive, first), second, first)
            };
            let (b, second_lower_bound, second_upper_bound) = if third <= fourth {
                (Metric::Range(Clusivity::Inclusive, third, Clusivity::Inclusive, fourth), third, fourth)
            } else {
                (Metric::Range(Clusivity::Inclusive, fourth, Clusivity::Inclusive, third), fourth, third)
            };
            let c = a.compose(&b);

            assert!(!c.is_satisfied(first_lower_bound + second_lower_bound));
            assert!(!c.is_satisfied(first_upper_bound + second_upper_bound));
            if first_lower_bound + second_lower_bound < candidate && candidate < first_upper_bound + second_upper_bound
            {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_exclusive_inclusive_range_compose_with_exclusive_exclusive_range() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let third: usize = u16::rand(&mut test_rng()) as usize;
            let fourth: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let (a, first_lower_bound, first_upper_bound) = if first <= second {
                (Metric::Range(Clusivity::Exclusive, first, Clusivity::Inclusive, second), first, second)
            } else {
                (Metric::Range(Clusivity::Exclusive, second, Clusivity::Inclusive, first), second, first)
            };
            let (b, second_lower_bound, second_upper_bound) = if third <= fourth {
                (Metric::Range(Clusivity::Exclusive, third, Clusivity::Exclusive, fourth), third, fourth)
            } else {
                (Metric::Range(Clusivity::Exclusive, fourth, Clusivity::Exclusive, third), fourth, third)
            };
            let c = a.compose(&b);

            assert!(!c.is_satisfied(first_lower_bound + second_lower_bound));
            assert!(!c.is_satisfied(first_upper_bound + second_upper_bound));
            if first_lower_bound + second_lower_bound < candidate && candidate < first_upper_bound + second_upper_bound
            {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_exclusive_inclusive_range_compose_with_exclusive_inclusive_range() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let third: usize = u16::rand(&mut test_rng()) as usize;
            let fourth: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let (a, first_lower_bound, first_upper_bound) = if first <= second {
                (Metric::Range(Clusivity::Exclusive, first, Clusivity::Inclusive, second), first, second)
            } else {
                (Metric::Range(Clusivity::Exclusive, second, Clusivity::Inclusive, first), second, first)
            };
            let (b, second_lower_bound, second_upper_bound) = if third <= fourth {
                (Metric::Range(Clusivity::Exclusive, third, Clusivity::Inclusive, fourth), third, fourth)
            } else {
                (Metric::Range(Clusivity::Exclusive, fourth, Clusivity::Inclusive, third), fourth, third)
            };
            let c = a.compose(&b);

            assert!(!c.is_satisfied(first_lower_bound + second_lower_bound));
            assert!(c.is_satisfied(first_upper_bound + second_upper_bound));
            if first_lower_bound + second_lower_bound < candidate && candidate <= first_upper_bound + second_upper_bound
            {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_exclusive_inclusive_range_compose_with_inclusive_exclusive_range() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let third: usize = u16::rand(&mut test_rng()) as usize;
            let fourth: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let (a, first_lower_bound, first_upper_bound) = if first <= second {
                (Metric::Range(Clusivity::Exclusive, first, Clusivity::Inclusive, second), first, second)
            } else {
                (Metric::Range(Clusivity::Exclusive, second, Clusivity::Inclusive, first), second, first)
            };
            let (b, second_lower_bound, second_upper_bound) = if third <= fourth {
                (Metric::Range(Clusivity::Inclusive, third, Clusivity::Exclusive, fourth), third, fourth)
            } else {
                (Metric::Range(Clusivity::Inclusive, fourth, Clusivity::Exclusive, third), fourth, third)
            };
            let c = a.compose(&b);

            assert!(!c.is_satisfied(first_lower_bound + second_lower_bound));
            assert!(!c.is_satisfied(first_upper_bound + second_upper_bound));
            if first_lower_bound + second_lower_bound < candidate && candidate < first_upper_bound + second_upper_bound
            {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_exclusive_inclusive_range_compose_with_inclusive_inclusive_range() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let third: usize = u16::rand(&mut test_rng()) as usize;
            let fourth: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let (a, first_lower_bound, first_upper_bound) = if first <= second {
                (Metric::Range(Clusivity::Exclusive, first, Clusivity::Inclusive, second), first, second)
            } else {
                (Metric::Range(Clusivity::Exclusive, second, Clusivity::Inclusive, first), second, first)
            };
            let (b, second_lower_bound, second_upper_bound) = if third <= fourth {
                (Metric::Range(Clusivity::Inclusive, third, Clusivity::Inclusive, fourth), third, fourth)
            } else {
                (Metric::Range(Clusivity::Inclusive, fourth, Clusivity::Inclusive, third), fourth, third)
            };
            let c = a.compose(&b);

            assert!(!c.is_satisfied(first_lower_bound + second_lower_bound));
            assert!(c.is_satisfied(first_upper_bound + second_upper_bound));
            if first_lower_bound + second_lower_bound < candidate && candidate <= first_upper_bound + second_upper_bound
            {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_inclusive_exclusive_range_compose_with_exclusive_exclusive_range() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let third: usize = u16::rand(&mut test_rng()) as usize;
            let fourth: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let (a, first_lower_bound, first_upper_bound) = if first <= second {
                (Metric::Range(Clusivity::Inclusive, first, Clusivity::Exclusive, second), first, second)
            } else {
                (Metric::Range(Clusivity::Inclusive, second, Clusivity::Exclusive, first), second, first)
            };
            let (b, second_lower_bound, second_upper_bound) = if third <= fourth {
                (Metric::Range(Clusivity::Exclusive, third, Clusivity::Exclusive, fourth), third, fourth)
            } else {
                (Metric::Range(Clusivity::Exclusive, fourth, Clusivity::Exclusive, third), fourth, third)
            };
            let c = a.compose(&b);

            assert!(!c.is_satisfied(first_lower_bound + second_lower_bound));
            assert!(!c.is_satisfied(first_upper_bound + second_upper_bound));
            if first_lower_bound + second_lower_bound < candidate && candidate < first_upper_bound + second_upper_bound
            {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_inclusive_exclusive_range_compose_with_exclusive_inclusive_range() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let third: usize = u16::rand(&mut test_rng()) as usize;
            let fourth: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let (a, first_lower_bound, first_upper_bound) = if first <= second {
                (Metric::Range(Clusivity::Inclusive, first, Clusivity::Exclusive, second), first, second)
            } else {
                (Metric::Range(Clusivity::Inclusive, second, Clusivity::Exclusive, first), second, first)
            };
            let (b, second_lower_bound, second_upper_bound) = if third <= fourth {
                (Metric::Range(Clusivity::Exclusive, third, Clusivity::Inclusive, fourth), third, fourth)
            } else {
                (Metric::Range(Clusivity::Exclusive, fourth, Clusivity::Inclusive, third), fourth, third)
            };
            let c = a.compose(&b);

            assert!(!c.is_satisfied(first_lower_bound + second_lower_bound));
            assert!(!c.is_satisfied(first_upper_bound + second_upper_bound));
            if first_lower_bound + second_lower_bound < candidate && candidate < first_upper_bound + second_upper_bound
            {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_inclusive_exclusive_range_compose_with_inclusive_exclusive_range() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let third: usize = u16::rand(&mut test_rng()) as usize;
            let fourth: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let (a, first_lower_bound, first_upper_bound) = if first <= second {
                (Metric::Range(Clusivity::Inclusive, first, Clusivity::Exclusive, second), first, second)
            } else {
                (Metric::Range(Clusivity::Inclusive, second, Clusivity::Exclusive, first), second, first)
            };
            let (b, second_lower_bound, second_upper_bound) = if third <= fourth {
                (Metric::Range(Clusivity::Inclusive, third, Clusivity::Exclusive, fourth), third, fourth)
            } else {
                (Metric::Range(Clusivity::Inclusive, fourth, Clusivity::Exclusive, third), fourth, third)
            };
            let c = a.compose(&b);

            assert!(c.is_satisfied(first_lower_bound + second_lower_bound));
            assert!(!c.is_satisfied(first_upper_bound + second_upper_bound));
            if first_lower_bound + second_lower_bound <= candidate && candidate < first_upper_bound + second_upper_bound
            {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_inclusive_exclusive_range_compose_with_inclusive_inclusive_range() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let third: usize = u16::rand(&mut test_rng()) as usize;
            let fourth: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let (a, first_lower_bound, first_upper_bound) = if first <= second {
                (Metric::Range(Clusivity::Inclusive, first, Clusivity::Exclusive, second), first, second)
            } else {
                (Metric::Range(Clusivity::Inclusive, second, Clusivity::Exclusive, first), second, first)
            };
            let (b, second_lower_bound, second_upper_bound) = if third <= fourth {
                (Metric::Range(Clusivity::Inclusive, third, Clusivity::Inclusive, fourth), third, fourth)
            } else {
                (Metric::Range(Clusivity::Inclusive, fourth, Clusivity::Inclusive, third), fourth, third)
            };
            let c = a.compose(&b);

            assert!(c.is_satisfied(first_lower_bound + second_lower_bound));
            assert!(!c.is_satisfied(first_upper_bound + second_upper_bound));
            if first_lower_bound + second_lower_bound <= candidate && candidate < first_upper_bound + second_upper_bound
            {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_inclusive_inclusive_range_compose_with_exclusive_exclusive_range() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let third: usize = u16::rand(&mut test_rng()) as usize;
            let fourth: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let (a, first_lower_bound, first_upper_bound) = if first <= second {
                (Metric::Range(Clusivity::Inclusive, first, Clusivity::Inclusive, second), first, second)
            } else {
                (Metric::Range(Clusivity::Inclusive, second, Clusivity::Inclusive, first), second, first)
            };
            let (b, second_lower_bound, second_upper_bound) = if third <= fourth {
                (Metric::Range(Clusivity::Exclusive, third, Clusivity::Exclusive, fourth), third, fourth)
            } else {
                (Metric::Range(Clusivity::Exclusive, fourth, Clusivity::Exclusive, third), fourth, third)
            };
            let c = a.compose(&b);

            assert!(!c.is_satisfied(first_lower_bound + second_lower_bound));
            assert!(!c.is_satisfied(first_upper_bound + second_upper_bound));
            if first_lower_bound + second_lower_bound < candidate && candidate < first_upper_bound + second_upper_bound
            {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_inclusive_inclusive_range_compose_with_exclusive_inclusive_range() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let third: usize = u16::rand(&mut test_rng()) as usize;
            let fourth: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let (a, first_lower_bound, first_upper_bound) = if first <= second {
                (Metric::Range(Clusivity::Inclusive, first, Clusivity::Inclusive, second), first, second)
            } else {
                (Metric::Range(Clusivity::Inclusive, second, Clusivity::Inclusive, first), second, first)
            };
            let (b, second_lower_bound, second_upper_bound) = if third <= fourth {
                (Metric::Range(Clusivity::Exclusive, third, Clusivity::Inclusive, fourth), third, fourth)
            } else {
                (Metric::Range(Clusivity::Exclusive, fourth, Clusivity::Inclusive, third), fourth, third)
            };
            let c = a.compose(&b);

            assert!(!c.is_satisfied(first_lower_bound + second_lower_bound));
            assert!(c.is_satisfied(first_upper_bound + second_upper_bound));
            if first_lower_bound + second_lower_bound < candidate && candidate <= first_upper_bound + second_upper_bound
            {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_inclusive_inclusive_range_compose_with_inclusive_exclusive_range() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let third: usize = u16::rand(&mut test_rng()) as usize;
            let fourth: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let (a, first_lower_bound, first_upper_bound) = if first <= second {
                (Metric::Range(Clusivity::Inclusive, first, Clusivity::Inclusive, second), first, second)
            } else {
                (Metric::Range(Clusivity::Inclusive, second, Clusivity::Inclusive, first), second, first)
            };
            let (b, second_lower_bound, second_upper_bound) = if third <= fourth {
                (Metric::Range(Clusivity::Inclusive, third, Clusivity::Exclusive, fourth), third, fourth)
            } else {
                (Metric::Range(Clusivity::Inclusive, fourth, Clusivity::Exclusive, third), fourth, third)
            };
            let c = a.compose(&b);

            assert!(c.is_satisfied(first_lower_bound + second_lower_bound));
            assert!(!c.is_satisfied(first_upper_bound + second_upper_bound));
            if first_lower_bound + second_lower_bound <= candidate && candidate < first_upper_bound + second_upper_bound
            {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_inclusive_inclusive_range_compose_with_inclusive_inclusive_range() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let third: usize = u16::rand(&mut test_rng()) as usize;
            let fourth: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let (a, first_lower_bound, first_upper_bound) = if first <= second {
                (Metric::Range(Clusivity::Inclusive, first, Clusivity::Inclusive, second), first, second)
            } else {
                (Metric::Range(Clusivity::Inclusive, second, Clusivity::Inclusive, first), second, first)
            };
            let (b, second_lower_bound, second_upper_bound) = if third <= fourth {
                (Metric::Range(Clusivity::Inclusive, third, Clusivity::Inclusive, fourth), third, fourth)
            } else {
                (Metric::Range(Clusivity::Inclusive, fourth, Clusivity::Inclusive, third), fourth, third)
            };
            let c = a.compose(&b);

            assert!(c.is_satisfied(first_lower_bound + second_lower_bound));
            assert!(c.is_satisfied(first_upper_bound + second_upper_bound));
            if first_lower_bound + second_lower_bound <= candidate
                && candidate <= first_upper_bound + second_upper_bound
            {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_exclusive_exclusive_range_compose_with_exclusive_upper_bound() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let third: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let (a, lower_bound, upper_bound) = if second <= third {
                (Metric::Range(Clusivity::Exclusive, second, Clusivity::Exclusive, third), second, third)
            } else {
                (Metric::Range(Clusivity::Exclusive, third, Clusivity::Exclusive, second), third, second)
            };
            let b = Metric::UpperBound(Clusivity::Exclusive, first);
            let c = a.compose(&b);

            assert!(!c.is_satisfied(lower_bound));
            assert!(!c.is_satisfied(first + upper_bound));
            if lower_bound < candidate && candidate < first + upper_bound {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_exclusive_inclusive_range_compose_with_exclusive_upper_bound() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let third: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let (a, lower_bound, upper_bound) = if second <= third {
                (Metric::Range(Clusivity::Exclusive, second, Clusivity::Inclusive, third), second, third)
            } else {
                (Metric::Range(Clusivity::Exclusive, third, Clusivity::Inclusive, second), third, second)
            };
            let b = Metric::UpperBound(Clusivity::Exclusive, first);
            let c = a.compose(&b);

            assert!(!c.is_satisfied(lower_bound));
            assert!(!c.is_satisfied(first + upper_bound));
            if lower_bound < candidate && candidate < first + upper_bound {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_inclusive_exclusive_range_compose_with_exclusive_upper_bound() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let third: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let (a, lower_bound, upper_bound) = if second <= third {
                (Metric::Range(Clusivity::Inclusive, second, Clusivity::Exclusive, third), second, third)
            } else {
                (Metric::Range(Clusivity::Inclusive, third, Clusivity::Exclusive, second), third, second)
            };
            let b = Metric::UpperBound(Clusivity::Exclusive, first);
            let c = a.compose(&b);

            assert!(c.is_satisfied(lower_bound));
            assert!(!c.is_satisfied(first + upper_bound));
            if lower_bound <= candidate && candidate < first + upper_bound {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_inclusive_inclusive_range_compose_with_exclusive_upper_bound() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let third: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let (a, lower_bound, upper_bound) = if second <= third {
                (Metric::Range(Clusivity::Inclusive, second, Clusivity::Inclusive, third), second, third)
            } else {
                (Metric::Range(Clusivity::Inclusive, third, Clusivity::Inclusive, second), third, second)
            };
            let b = Metric::UpperBound(Clusivity::Exclusive, first);
            let c = a.compose(&b);

            assert!(c.is_satisfied(lower_bound));
            assert!(!c.is_satisfied(first + upper_bound));
            if lower_bound <= candidate && candidate < first + upper_bound {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_exclusive_exclusive_range_compose_with_inclusive_upper_bound() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let third: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let (a, lower_bound, upper_bound) = if second <= third {
                (Metric::Range(Clusivity::Exclusive, second, Clusivity::Exclusive, third), second, third)
            } else {
                (Metric::Range(Clusivity::Exclusive, third, Clusivity::Exclusive, second), third, second)
            };
            let b = Metric::UpperBound(Clusivity::Inclusive, first);
            let c = a.compose(&b);

            assert!(!c.is_satisfied(lower_bound));
            assert!(!c.is_satisfied(first + upper_bound));
            if lower_bound < candidate && candidate < first + upper_bound {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_exclusive_inclusive_range_compose_with_inclusive_upper_bound() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let third: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let (a, lower_bound, upper_bound) = if second <= third {
                (Metric::Range(Clusivity::Exclusive, second, Clusivity::Inclusive, third), second, third)
            } else {
                (Metric::Range(Clusivity::Exclusive, third, Clusivity::Inclusive, second), third, second)
            };
            let b = Metric::UpperBound(Clusivity::Inclusive, first);
            let c = a.compose(&b);

            assert!(!c.is_satisfied(lower_bound));
            assert!(c.is_satisfied(first + upper_bound));
            if lower_bound < candidate && candidate <= first + upper_bound {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_inclusive_exclusive_range_compose_with_inclusive_upper_bound() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let third: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let (a, lower_bound, upper_bound) = if second <= third {
                (Metric::Range(Clusivity::Inclusive, second, Clusivity::Exclusive, third), second, third)
            } else {
                (Metric::Range(Clusivity::Inclusive, third, Clusivity::Exclusive, second), third, second)
            };
            let b = Metric::UpperBound(Clusivity::Inclusive, first);
            let c = a.compose(&b);

            assert!(c.is_satisfied(lower_bound));
            assert!(!c.is_satisfied(first + upper_bound));
            if lower_bound <= candidate && candidate < first + upper_bound {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_inclusive_inclusive_range_compose_with_inclusive_upper_bound() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let third: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let (a, lower_bound, upper_bound) = if second <= third {
                (Metric::Range(Clusivity::Inclusive, second, Clusivity::Inclusive, third), second, third)
            } else {
                (Metric::Range(Clusivity::Inclusive, third, Clusivity::Inclusive, second), third, second)
            };
            let b = Metric::UpperBound(Clusivity::Inclusive, first);
            let c = a.compose(&b);

            assert!(c.is_satisfied(lower_bound));
            assert!(c.is_satisfied(first + upper_bound));
            if lower_bound <= candidate && candidate <= first + upper_bound {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_exclusive_upper_bound_compose_with_exact() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let a = Metric::UpperBound(Clusivity::Exclusive, second);
            let b = Metric::Exact(first);
            let c = a.compose(&b);

            assert!(!c.is_satisfied(first + second));
            if candidate < first + second {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_inclusive_upper_bound_compose_with_exact() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let a = Metric::UpperBound(Clusivity::Inclusive, second);
            let b = Metric::Exact(first);
            let c = a.compose(&b);

            assert!(c.is_satisfied(first + second));
            if candidate <= first + second {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_exclusive_upper_bound_compose_with_exclusive_exclusive_range() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let third: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let a = Metric::UpperBound(Clusivity::Exclusive, first);
            let (b, lower_bound, upper_bound) = if second <= third {
                (Metric::Range(Clusivity::Exclusive, second, Clusivity::Exclusive, third), second, third)
            } else {
                (Metric::Range(Clusivity::Exclusive, third, Clusivity::Exclusive, second), third, second)
            };
            let c = a.compose(&b);

            assert!(!c.is_satisfied(lower_bound));
            assert!(!c.is_satisfied(first + upper_bound));
            if lower_bound < candidate && candidate < first + upper_bound {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_exclusive_upper_bound_compose_with_exclusive_inclusive_range() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let third: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let a = Metric::UpperBound(Clusivity::Exclusive, first);
            let (b, lower_bound, upper_bound) = if second <= third {
                (Metric::Range(Clusivity::Exclusive, second, Clusivity::Inclusive, third), second, third)
            } else {
                (Metric::Range(Clusivity::Exclusive, third, Clusivity::Inclusive, second), third, second)
            };
            let c = a.compose(&b);

            assert!(!c.is_satisfied(lower_bound));
            assert!(!c.is_satisfied(first + upper_bound));
            if lower_bound < candidate && candidate < first + upper_bound {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_exclusive_upper_bound_compose_with_inclusive_exclusive_range() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let third: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let a = Metric::UpperBound(Clusivity::Exclusive, first);
            let (b, lower_bound, upper_bound) = if second <= third {
                (Metric::Range(Clusivity::Inclusive, second, Clusivity::Exclusive, third), second, third)
            } else {
                (Metric::Range(Clusivity::Inclusive, third, Clusivity::Exclusive, second), third, second)
            };
            let c = a.compose(&b);

            assert!(c.is_satisfied(lower_bound));
            assert!(!c.is_satisfied(first + upper_bound));
            if lower_bound <= candidate && candidate < first + upper_bound {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_exclusive_upper_bound_compose_with_inclusive_inclusive_range() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let third: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let a = Metric::UpperBound(Clusivity::Exclusive, first);
            let (b, lower_bound, upper_bound) = if second <= third {
                (Metric::Range(Clusivity::Inclusive, second, Clusivity::Inclusive, third), second, third)
            } else {
                (Metric::Range(Clusivity::Inclusive, third, Clusivity::Inclusive, second), third, second)
            };
            let c = a.compose(&b);

            assert!(c.is_satisfied(lower_bound));
            assert!(!c.is_satisfied(first + upper_bound));
            if lower_bound <= candidate && candidate < first + upper_bound {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_inclusive_upper_bound_compose_with_exclusive_exclusive_range() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let third: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let a = Metric::UpperBound(Clusivity::Inclusive, first);
            let (b, lower_bound, upper_bound) = if second <= third {
                (Metric::Range(Clusivity::Exclusive, second, Clusivity::Exclusive, third), second, third)
            } else {
                (Metric::Range(Clusivity::Exclusive, third, Clusivity::Exclusive, second), third, second)
            };
            let c = a.compose(&b);

            assert!(!c.is_satisfied(lower_bound));
            assert!(!c.is_satisfied(first + upper_bound));
            if lower_bound < candidate && candidate < first + upper_bound {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_inclusive_upper_bound_compose_with_exclusive_inclusive_range() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let third: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let a = Metric::UpperBound(Clusivity::Inclusive, first);
            let (b, lower_bound, upper_bound) = if second <= third {
                (Metric::Range(Clusivity::Exclusive, second, Clusivity::Inclusive, third), second, third)
            } else {
                (Metric::Range(Clusivity::Exclusive, third, Clusivity::Inclusive, second), third, second)
            };
            let c = a.compose(&b);

            assert!(!c.is_satisfied(lower_bound));
            assert!(c.is_satisfied(first + upper_bound));
            if lower_bound < candidate && candidate <= first + upper_bound {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_inclusive_upper_bound_compose_with_inclusive_exclusive_range() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let third: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let a = Metric::UpperBound(Clusivity::Inclusive, first);
            let (b, lower_bound, upper_bound) = if second <= third {
                (Metric::Range(Clusivity::Inclusive, second, Clusivity::Exclusive, third), second, third)
            } else {
                (Metric::Range(Clusivity::Inclusive, third, Clusivity::Exclusive, second), third, second)
            };
            let c = a.compose(&b);

            assert!(c.is_satisfied(lower_bound));
            assert!(!c.is_satisfied(first + upper_bound));
            if lower_bound <= candidate && candidate < first + upper_bound {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_inclusive_upper_bound_compose_with_inclusive_inclusive_range() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let third: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let a = Metric::UpperBound(Clusivity::Inclusive, first);
            let (b, lower_bound, upper_bound) = if second <= third {
                (Metric::Range(Clusivity::Inclusive, second, Clusivity::Inclusive, third), second, third)
            } else {
                (Metric::Range(Clusivity::Inclusive, third, Clusivity::Inclusive, second), third, second)
            };
            let c = a.compose(&b);

            assert!(c.is_satisfied(lower_bound));
            assert!(c.is_satisfied(first + upper_bound));
            if lower_bound <= candidate && candidate <= first + upper_bound {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_exclusive_upper_bound_compose_with_exclusive_upper_bound() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let a = Metric::UpperBound(Clusivity::Exclusive, second);
            let b = Metric::UpperBound(Clusivity::Exclusive, first);
            let c = a.compose(&b);

            assert!(!c.is_satisfied(first + second));
            if candidate < first + second {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_exclusive_upper_bound_compose_with_inclusive_upper_bound() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let a = Metric::UpperBound(Clusivity::Exclusive, second);
            let b = Metric::UpperBound(Clusivity::Inclusive, first);
            let c = a.compose(&b);

            assert!(!c.is_satisfied(first + second));
            if candidate < first + second {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_inclusive_upper_bound_compose_with_exclusive_upper_bound() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let a = Metric::UpperBound(Clusivity::Inclusive, second);
            let b = Metric::UpperBound(Clusivity::Exclusive, first);
            let c = a.compose(&b);

            assert!(!c.is_satisfied(first + second));
            if candidate < first + second {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }

    #[test]
    fn test_inclusive_upper_bound_compose_with_inclusive_upper_bound() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let a = Metric::UpperBound(Clusivity::Inclusive, second);
            let b = Metric::UpperBound(Clusivity::Inclusive, first);
            let c = a.compose(&b);

            assert!(c.is_satisfied(first + second));
            if candidate <= first + second {
                assert!(c.is_satisfied(candidate));
            } else {
                assert!(!c.is_satisfied(candidate));
            }
        }
    }
}
