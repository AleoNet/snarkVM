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

impl<E: Environment> Equal<Self> for StringType<E> {
    type Output = Boolean<E>;

    /// Returns `true` if `self` and `other` are equal.
    fn is_equal(&self, other: &Self) -> Self::Output {
        self.to_fields()
            .iter()
            .zip_eq(&other.to_fields())
            .fold(Boolean::constant(true), |acc, (a, b)| acc & a.is_equal(b))
    }

    /// Returns `true` if `self` and `other` are *not* equal.
    fn is_not_equal(&self, other: &Self) -> Self::Output {
        self.to_fields()
            .iter()
            .zip_eq(&other.to_fields())
            .fold(Boolean::constant(false), |acc, (a, b)| acc | a.is_not_equal(b))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    use rand::Rng;

    fn sample_string(mode: Mode) -> StringType<Circuit> {
        let rng = &mut test_rng();

        // Sample a random string. Take 1/4th to ensure we fit for all code points.
        let given: String = (0..Circuit::NUM_STRING_BYTES / 4).map(|_| rng.gen::<char>()).collect();
        StringType::<Circuit>::new(mode, console::StringType::new(&given))
    }

    fn check_is_equal(
        mode: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) -> Result<()> {
        // Sample two strings.
        let string_a = sample_string(mode);
        let string_b = sample_string(mode);

        Circuit::scope(&format!("{}", mode), || {
            let candidate = string_a.is_equal(&string_a);
            assert!(candidate.eject_value());
            assert_scope!(num_constants, num_public, num_private, num_constraints);
        });

        Circuit::scope(&format!("{}", mode), || {
            let candidate = string_a.is_equal(&string_b);
            assert!(!candidate.eject_value());
            assert_scope!(num_constants, num_public, num_private, num_constraints);
        });

        Circuit::reset();
        Ok(())
    }

    fn check_is_not_equal(
        mode: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) -> Result<()> {
        // Sample two strings.
        let string_a = sample_string(mode);
        let string_b = sample_string(mode);

        Circuit::scope(&format!("{}", mode), || {
            let candidate = string_a.is_not_equal(&string_b);
            assert!(candidate.eject_value());
            assert_scope!(num_constants, num_public, num_private, num_constraints);
        });

        Circuit::scope(&format!("{}", mode), || {
            let candidate = string_a.is_not_equal(&string_a);
            assert!(!candidate.eject_value());
            assert_scope!(num_constants, num_public, num_private, num_constraints);
        });

        Circuit::reset();
        Ok(())
    }

    #[test]
    fn test_is_equal_constant() -> Result<()> {
        check_is_equal(Mode::Constant, 8, 0, 0, 0)
    }

    #[test]
    fn test_is_equal_public() -> Result<()> {
        check_is_equal(Mode::Public, 0, 0, 23, 31)
    }

    #[test]
    fn test_is_equal_private() -> Result<()> {
        check_is_equal(Mode::Private, 0, 0, 23, 31)
    }

    #[test]
    fn test_is_not_equal_constant() -> Result<()> {
        check_is_not_equal(Mode::Constant, 8, 0, 0, 0)
    }

    #[test]
    fn test_is_not_equal_public() -> Result<()> {
        check_is_not_equal(Mode::Public, 0, 0, 23, 31)
    }

    #[test]
    fn test_is_not_equal_private() -> Result<()> {
        check_is_not_equal(Mode::Private, 0, 0, 23, 31)
    }
}
