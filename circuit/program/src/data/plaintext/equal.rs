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

impl<A: Aleo> Equal<Self> for Plaintext<A> {
    type Output = Boolean<A>;

    /// Returns `true` if `self` and `other` are equal.
    fn is_equal(&self, other: &Self) -> Self::Output {
        match (self, other) {
            (Self::Literal(a, _), Self::Literal(b, _)) => a.is_equal(b),
            (Self::Struct(a, _), Self::Struct(b, _)) => match a.len() == b.len() {
                true => {
                    // Recursively check each member for equality.
                    let mut equal = Boolean::constant(true);
                    for ((name_a, plaintext_a), (name_b, plaintext_b)) in a.iter().zip_eq(b.iter()) {
                        equal = equal & name_a.is_equal(name_b) & plaintext_a.is_equal(plaintext_b);
                    }
                    equal
                }
                false => Boolean::constant(false),
            },
            (Self::Literal(..), _) | (Self::Struct(..), _) => Boolean::constant(false),
        }
    }

    /// Returns `true` if `self` and `other` are *not* equal.
    fn is_not_equal(&self, other: &Self) -> Self::Output {
        match (self, other) {
            (Self::Literal(a, _), Self::Literal(b, _)) => a.is_not_equal(b),
            (Self::Struct(a, _), Self::Struct(b, _)) => match a.len() == b.len() {
                true => {
                    // Recursively check each member for inequality.
                    let mut not_equal = Boolean::constant(false);
                    for ((name_a, plaintext_a), (name_b, plaintext_b)) in a.iter().zip_eq(b.iter()) {
                        not_equal = not_equal | name_a.is_not_equal(name_b) | plaintext_a.is_not_equal(plaintext_b);
                    }
                    not_equal
                }
                false => Boolean::constant(true),
            },
            (Self::Literal(..), _) | (Self::Struct(..), _) => Boolean::constant(true),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;

    fn sample_plaintext(mode: Mode) -> Plaintext<Circuit> {
        let plaintext = console::Plaintext::<<Circuit as Environment>::Network>::from_str(
            r"{
    a: true,
    b: 123456789field,
    c: 0group,
    d: {
        e: true,
        f: 123456789field,
        g: 0group
    }
}",
        )
        .unwrap();
        Plaintext::new(mode, plaintext)
    }

    fn sample_mismatched_plaintext(mode: Mode) -> Plaintext<Circuit> {
        let plaintext = console::Plaintext::<<Circuit as Environment>::Network>::from_str(
            r"{
    a: false,
    b: 123456789field,
    c: 0group,
    d: {
        e: true,
        f: 123456789field,
        g: 0group
    }
}",
        )
        .unwrap();
        Plaintext::new(mode, plaintext)
    }

    fn check_is_equal(
        mode: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) -> Result<()> {
        // Sample the plaintext.
        let plaintext = sample_plaintext(mode);
        let mismatched_plaintext = sample_mismatched_plaintext(mode);

        Circuit::scope(&format!("{}", mode), || {
            let candidate = plaintext.is_equal(&plaintext);
            assert!(candidate.eject_value());
            assert_scope!(num_constants, num_public, num_private, num_constraints);
        });

        Circuit::scope(&format!("{}", mode), || {
            let candidate = plaintext.is_equal(&mismatched_plaintext);
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
        // Sample the plaintext.
        let plaintext = sample_plaintext(mode);
        let mismatched_plaintext = sample_mismatched_plaintext(mode);

        Circuit::scope(&format!("{}", mode), || {
            let candidate = plaintext.is_not_equal(&mismatched_plaintext);
            assert!(candidate.eject_value());
            assert_scope!(num_constants, num_public, num_private, num_constraints);
        });

        Circuit::scope(&format!("{}", mode), || {
            let candidate = plaintext.is_not_equal(&plaintext);
            assert!(!candidate.eject_value());
            assert_scope!(num_constants, num_public, num_private, num_constraints);
        });

        Circuit::reset();
        Ok(())
    }

    #[test]
    fn test_is_equal_constant() -> Result<()> {
        check_is_equal(Mode::Constant, 13, 0, 0, 0)
    }

    #[test]
    fn test_is_equal_public() -> Result<()> {
        check_is_equal(Mode::Public, 7, 0, 21, 27)
    }

    #[test]
    fn test_is_equal_private() -> Result<()> {
        check_is_equal(Mode::Private, 7, 0, 21, 27)
    }

    #[test]
    fn test_is_not_equal_constant() -> Result<()> {
        check_is_not_equal(Mode::Constant, 13, 0, 0, 0)
    }

    #[test]
    fn test_is_not_equal_public() -> Result<()> {
        check_is_not_equal(Mode::Public, 7, 0, 21, 27)
    }

    #[test]
    fn test_is_not_equal_private() -> Result<()> {
        check_is_not_equal(Mode::Private, 7, 0, 21, 27)
    }
}
