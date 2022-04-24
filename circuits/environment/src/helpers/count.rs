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

use core::{fmt::Debug, ops::Add};

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

/// A `Measurement` is a quantity that can be measured.
/// The variants of the `Measurement` defines a condition associated with the measurable quantity.
#[derive(Clone, Debug)]
pub enum Measurement<V: Ord + Add<Output = V>> {
    Exact(V),
    Range(V, V),
    UpperBound(V),
}

impl<V: Ord + Add<Output = V> + Copy + Debug> Measurement<V> {
    /// TODO (howardwu): Deprecate this method and implement `PartialEq` & `Eq`.
    /// Returns `true` if the value matches the metric.
    /// For an `Exact` metric, `value` must be equal to the exact value defined by the metric.
    /// For a `Range` metric, `value` must be satisfy lower bound and the upper bound.
    /// For an `UpperBound` metric, `value` must be satisfy the upper bound.
    pub fn matches(&self, candidate: V) -> bool {
        let outcome = match self {
            Measurement::Exact(expected) => *expected == candidate,
            Measurement::Range(lower, upper) => candidate > *lower && candidate < *upper,
            Measurement::UpperBound(bound) => candidate < *bound,
        };

        if !outcome {
            eprintln!("{:?} does not match {:?}", candidate, self);
        }

        outcome
    }

    /// TODO (howardwu): Deprecate this method and implement `Add` operation.
    /// Composes two variants of `Measurement` and returns the resulting `Measurement`.
    /// The composition is defined such that if a value `a` satisfies `self` and a value `b` satisfies `other`,
    /// then `a + b` satisfies the resulting `Measurement`.
    pub fn compose(&self, other: &Self) -> Self {
        match (self, other) {
            // `Exact` + `Exact` => `Exact`
            (Measurement::Exact(exact_a), Measurement::Exact(exact_b)) => Measurement::Exact(*exact_a + *exact_b),
            // `Range` + `Range` => `Range`
            (Measurement::Range(lower_a, upper_a), Measurement::Range(lower_b, upper_b)) => {
                Measurement::Range(*lower_a + *lower_b, *upper_a + *upper_b)
            }
            // `UpperBound` + `UpperBound` => `UpperBound`
            (Measurement::UpperBound(upper_a), Measurement::UpperBound(upper_b)) => {
                Measurement::UpperBound(*upper_a + *upper_b)
            }
            // `Exact` + `Range` => `Range`
            // `Range` + `Exact` => `Range`
            (Measurement::Exact(exact), Measurement::Range(lower, upper))
            | (Measurement::Range(lower, upper), Measurement::Exact(exact)) => {
                Measurement::Range(*exact + *lower, *exact + *upper)
            }
            // `Exact` + `UpperBound` => `UpperBound`
            // `UpperBound` + `Exact` => `UpperBound`
            (Measurement::Exact(exact), Measurement::UpperBound(upper))
            | (Measurement::UpperBound(upper), Measurement::Exact(exact)) => Measurement::UpperBound(*exact + *upper),
            // `Range` + `UpperBound` => `Range`
            // `UpperBound` + `Range` => `Range`
            (Measurement::Range(lower, upper_a), Measurement::UpperBound(upper_b))
            | (Measurement::UpperBound(upper_a), Measurement::Range(lower, upper_b)) => {
                Measurement::Range(*lower, *upper_a + *upper_b)
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
    fn test_exact_matches() {
        for _ in 0..ITERATIONS {
            // Generate a random `Measurement` and candidate value.
            let value: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;
            let metric = Measurement::Exact(value);

            // Check that the metric is only satisfied if the candidate is equal to the value.
            assert!(metric.matches(value));
            if candidate == value {
                assert!(metric.matches(candidate));
            } else {
                assert!(!metric.matches(candidate));
            }
        }
    }

    #[test]
    fn test_range_matches() {
        for _ in 0..ITERATIONS {
            // Generate a random `Measurement::UpperBound` and candidate value.
            let first_bound: usize = u16::rand(&mut test_rng()) as usize;
            let second_bound: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;
            let (metric, lower, upper) = if first_bound <= second_bound {
                (Measurement::Range(first_bound, second_bound), first_bound, second_bound)
            } else {
                (Measurement::Range(second_bound, first_bound), second_bound, first_bound)
            };

            // Check that the metric is only satisfied if the candidate is less than upper.
            assert!(!metric.matches(lower));
            assert!(!metric.matches(upper));
            if lower < candidate && candidate < upper {
                assert!(metric.matches(candidate));
            } else {
                assert!(!metric.matches(candidate));
            }
        }
    }

    #[test]
    fn test_upper_matches() {
        for _ in 0..ITERATIONS {
            // Generate a random `Measurement::UpperBound` and candidate value.
            let upper: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;
            let metric = Measurement::UpperBound(upper);

            // Check that the metric is only satisfied if the candidate is less than upper.
            assert!(!metric.matches(upper));
            if candidate < upper {
                assert!(metric.matches(candidate));
            } else {
                assert!(!metric.matches(candidate));
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

            let a = Measurement::Exact(first);
            let b = Measurement::Exact(second);
            let c = a.compose(&b);

            assert!(c.matches(first + second));
            if candidate == first + second {
                assert!(c.matches(candidate));
            } else {
                assert!(!c.matches(candidate));
            }
        }
    }

    #[test]
    fn test_exact_compose_with_range() {
        let value: usize = u16::rand(&mut test_rng()) as usize;
        let first_bound: usize = u16::rand(&mut test_rng()) as usize;
        let second_bound: usize = u16::rand(&mut test_rng()) as usize;
        let candidate: usize = u16::rand(&mut test_rng()) as usize;

        let a = Measurement::Exact(value);
        let (b, lower, upper) = if first_bound <= second_bound {
            (Measurement::Range(first_bound, second_bound), first_bound, second_bound)
        } else {
            (Measurement::Range(second_bound, first_bound), second_bound, first_bound)
        };
        let c = a.compose(&b);

        assert!(!c.matches(value + lower));
        assert!(!c.matches(value + upper));
        if value + lower < candidate && candidate < value + upper {
            assert!(c.matches(candidate));
        } else {
            assert!(!c.matches(candidate));
        }
    }

    #[test]
    fn test_exact_compose_with_upper() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let a = Measurement::Exact(first);
            let b = Measurement::UpperBound(second);
            let c = a.compose(&b);

            assert!(!c.matches(first + second));
            if candidate < first + second {
                assert!(c.matches(candidate));
            } else {
                assert!(!c.matches(candidate));
            }
        }
    }

    #[test]
    fn test_range_compose_with_exact() {
        let value: usize = u16::rand(&mut test_rng()) as usize;
        let first_bound: usize = u16::rand(&mut test_rng()) as usize;
        let second_bound: usize = u16::rand(&mut test_rng()) as usize;
        let candidate: usize = u16::rand(&mut test_rng()) as usize;

        let (a, lower, upper) = if first_bound <= second_bound {
            (Measurement::Range(first_bound, second_bound), first_bound, second_bound)
        } else {
            (Measurement::Range(second_bound, first_bound), second_bound, first_bound)
        };
        let b = Measurement::Exact(value);
        let c = a.compose(&b);

        assert!(!c.matches(value + lower));
        assert!(!c.matches(value + upper));
        if value + lower < candidate && candidate < value + upper {
            assert!(c.matches(candidate));
        } else {
            assert!(!c.matches(candidate));
        }
    }

    #[test]
    fn test_range_compose_with_range() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let third: usize = u16::rand(&mut test_rng()) as usize;
            let fourth: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let (a, first_lower, first_upper) = if first <= second {
                (Measurement::Range(first, second), first, second)
            } else {
                (Measurement::Range(second, first), second, first)
            };
            let (b, second_lower, second_upper) = if third <= fourth {
                (Measurement::Range(third, fourth), third, fourth)
            } else {
                (Measurement::Range(fourth, third), fourth, third)
            };
            let c = a.compose(&b);

            assert!(!c.matches(first_lower + second_lower));
            assert!(!c.matches(first_upper + second_upper));
            if first_lower + second_lower < candidate && candidate < first_upper + second_upper {
                assert!(c.matches(candidate));
            } else {
                assert!(!c.matches(candidate));
            }
        }
    }

    #[test]
    fn test_range_compose_with_upper() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let third: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let (a, lower, upper) = if second <= third {
                (Measurement::Range(second, third), second, third)
            } else {
                (Measurement::Range(third, second), third, second)
            };
            let b = Measurement::UpperBound(first);
            let c = a.compose(&b);

            assert!(!c.matches(lower));
            assert!(!c.matches(first + upper));
            if lower < candidate && candidate < first + upper {
                assert!(c.matches(candidate));
            } else {
                assert!(!c.matches(candidate));
            }
        }
    }

    #[test]
    fn test_upper_compose_with_exact() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let a = Measurement::UpperBound(second);
            let b = Measurement::Exact(first);
            let c = a.compose(&b);

            assert!(!c.matches(first + second));
            if candidate < first + second {
                assert!(c.matches(candidate));
            } else {
                assert!(!c.matches(candidate));
            }
        }
    }

    #[test]
    fn test_upper_compose_with_range() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let third: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let a = Measurement::UpperBound(first);
            let (b, lower, upper) = if second <= third {
                (Measurement::Range(second, third), second, third)
            } else {
                (Measurement::Range(third, second), third, second)
            };
            let c = a.compose(&b);

            assert!(!c.matches(lower));
            assert!(!c.matches(first + upper));
            if lower < candidate && candidate < first + upper {
                assert!(c.matches(candidate));
            } else {
                assert!(!c.matches(candidate));
            }
        }
    }

    #[test]
    fn test_upper_compose_with_upper() {
        for _ in 0..ITERATIONS {
            let first: usize = u16::rand(&mut test_rng()) as usize;
            let second: usize = u16::rand(&mut test_rng()) as usize;
            let candidate: usize = u16::rand(&mut test_rng()) as usize;

            let a = Measurement::UpperBound(second);
            let b = Measurement::UpperBound(first);
            let c = a.compose(&b);

            assert!(!c.matches(first + second));
            if candidate < first + second {
                assert!(c.matches(candidate));
            } else {
                assert!(!c.matches(candidate));
            }
        }
    }
}
