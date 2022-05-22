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

use super::*;

impl<E: Environment> Compare<Field<E>> for Field<E> {
    type Output = Boolean<E>;

    /// Returns `true` if `self` is less than `other`.
    fn is_less_than(&self, other: &Self) -> Self::Output {
        if self.is_constant() && other.is_constant() {
            Boolean::constant(self.eject_value() < other.eject_value())
        } else if self.is_constant() {
            // (For advanced users) this implementation saves us from instantiating 253 constants for
            // the bits of `self`. The implementation in the `else` case invokes `to_bits_le` on
            // `self` which would allocate 253 constants. Since `self` is constant, we can directly
            // inspect its bits and construct an equivalent ternary expression to that in the `else`
            // case. We describe the logic below:
            // - If `self_bit` is `true`, then `self` is less than `other` iff `other_bit` is `true` and `rest_is_less` is `true.
            // - If `self_bit` is `false`, then `self` is less than `other` iff `other_bit` is `true` or `rest_is_less` is `true`.
            self.eject_value().to_bits_le().into_iter().zip_eq(other.to_bits_le()).fold(
                Boolean::constant(false),
                |rest_is_less, (self_bit, other_bit)| {
                    if self_bit { other_bit.bitand(&rest_is_less) } else { other_bit.bitor(&rest_is_less) }
                },
            )
        } else if other.is_constant() {
            // (For advanced users) this implementation saves us from instantiating 253 constants for
            // the bits of `self`. The implementation in the `else` case invokes `to_bits_le` on
            // `self` which would allocate 253 constants. Since `self` is constant, we can directly
            // inspect its bits and construct an equivalent ternary expression to that in the `else`
            // case. We describe the logic below:
            // - If `other_bit` is `true`, then `self` is less than `other` iff `self_bit` is `false` or `rest_is_less` is `true.
            // - If `other_bit` is `false`, then `self` is less than `other` iff `self_bit` is `false` and `rest_is_less` is `true`.
            self.to_bits_le().into_iter().zip_eq(other.eject_value().to_bits_le()).fold(
                Boolean::constant(false),
                |rest_is_less, (self_bit, other_bit)| {
                    if other_bit { (!self_bit).bitor(rest_is_less) } else { (!self_bit).bitand(&rest_is_less) }
                },
            )
        } else {
            // Zip `self.to_bits_le()` and `other.to_bits_le()` together and construct a check on the sequence of bit pairs.
            // The bitwise check begins with the most-significant bit pair and ends with the least-significant bit pair.
            // For each bit pair,
            // - If `self_bit` and `other_bit` are different signs, then if `self_bit` is `true`, return false.
            // - If `self_bit` and `other_bit` are different signs, then if `self_bit` is `false`, return true.
            // - If `self_bit` and `other_bit` are the same sign, then check the following bits.
            //
            // The truth table is as follows:
            // | self_bit | other_bit | rest_is_less | result |
            // |----------+-----------+--------------+--------|
            // | `true`   | `true`    | `true`       | `true` |
            // | `true`   | `true`    | `false`      | `false`|
            // | `true`   | `false`   | `true`       | `true` |
            // | `true`   | `false`   | `false`      | `true` |
            // | `false`  | `true`    | `true`       | `false`|
            // | `false`  | `true`    | `false`      | `false`|
            // | `false`  | `false`   | `true`       | `true` |
            // | `false`  | `false`   | `false`      | `false`|
            //
            self.to_bits_le().iter().zip_eq(other.to_bits_le()).fold(
                Boolean::constant(false),
                |rest_is_less, (self_bit, other_bit)| {
                    Boolean::ternary(&self_bit.bitxor(&other_bit), &other_bit, &rest_is_less)
                },
            )
        }
    }

    /// Returns `true` if `self` is greater than `other`.
    fn is_greater_than(&self, other: &Self) -> Self::Output {
        other.is_less_than(self)
    }

    /// Returns `true` if `self` is less than or equal to `other`.
    fn is_less_than_or_equal(&self, other: &Self) -> Self::Output {
        other.is_greater_than_or_equal(self)
    }

    /// Returns `true` if `self` is greater than or equal to `other`.
    fn is_greater_than_or_equal(&self, other: &Self) -> Self::Output {
        !self.is_less_than(other)
    }
}

// TODO: Implement `Metrics` and `OutputMode` for `Compare`. Waiting for PR#711  to land as it significantly changes the counts.

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: u64 = 100;

    fn check_is_less_than(
        name: &str,
        expected: bool,
        a: &Field<Circuit>,
        b: &Field<Circuit>,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) {
        // Perform the less than comparison.
        Circuit::scope(name, || {
            println!("{}", name);
            println!("  a: {}", a);
            println!("  b: {}", b);
            println!("  expected: {}", expected);
            let candidate = a.is_less_than(b);
            assert_eq!(expected, candidate.eject_value());
            match (a.eject_mode(), b.eject_mode()) {
                (Mode::Constant, Mode::Constant) => {
                    assert_scope!(num_constants, num_public, num_private, num_constraints)
                }
                (_, Mode::Constant) | (Mode::Constant, _) => {
                    assert_scope!(<=num_constants, <=num_public, <=num_private, <=num_constraints)
                }
                _ => assert_scope!(num_constants, num_public, num_private, num_constraints),
            }
        });
        Circuit::reset();
    }

    fn run_test(
        mode_a: Mode,
        mode_b: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::BaseField = UniformRand::rand(&mut test_rng());
            let second: <Circuit as Environment>::BaseField = UniformRand::rand(&mut test_rng());

            let a = Field::<Circuit>::new(mode_a, first);
            let b = Field::<Circuit>::new(mode_b, second);
            let expected = first < second;
            let name = format!("{} {} {}", mode_a, mode_b, i);
            check_is_less_than(&name, expected, &a, &b, num_constants, num_public, num_private, num_constraints);

            // Check `first` is not less than `first`.
            let a = Field::<Circuit>::new(mode_a, first);
            let b = Field::<Circuit>::new(mode_b, first);
            check_is_less_than(
                "first !< first",
                false,
                &a,
                &b,
                num_constants,
                num_public,
                num_private,
                num_constraints,
            );
        }
    }

    #[test]
    fn test_constant_is_less_than_constant() {
        run_test(Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_constant_is_less_than_public() {
        run_test(Mode::Constant, Mode::Public, 0, 0, 506, 507);
    }

    #[test]
    fn test_constant_is_less_than_private() {
        run_test(Mode::Constant, Mode::Private, 0, 0, 506, 507);
    }

    #[test]
    fn test_public_is_less_than_constant() {
        run_test(Mode::Public, Mode::Constant, 0, 0, 506, 507);
    }

    #[test]
    fn test_public_is_less_than_public() {
        run_test(Mode::Public, Mode::Public, 0, 0, 1012, 1014);
    }

    #[test]
    fn test_public_is_less_than_private() {
        run_test(Mode::Public, Mode::Private, 0, 0, 1012, 1014);
    }

    #[test]
    fn test_private_is_less_than_constant() {
        run_test(Mode::Private, Mode::Constant, 0, 0, 506, 507);
    }

    #[test]
    fn test_private_is_less_than_public() {
        run_test(Mode::Private, Mode::Public, 0, 0, 1012, 1014);
    }

    #[test]
    fn test_private_is_less_than_private() {
        run_test(Mode::Private, Mode::Private, 0, 0, 1012, 1014);
    }
}
