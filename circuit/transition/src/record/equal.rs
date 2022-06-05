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

impl<A: Aleo> Equal<Self> for Record<A> {
    type Output = Boolean<A>;

    /// Returns `true` if `self` and `other` are equal.
    fn is_equal(&self, other: &Self) -> Self::Output {
        self.owner.is_equal(&other.owner)
            & self.balance.is_equal(&other.balance)
            & self.data.is_equal(&other.data)
            & self.nonce.is_equal(&other.nonce)
            & self.mac.is_equal(&other.mac)
            & self.bcm.is_equal(&other.bcm)
    }

    /// Returns `true` if `self` and `other` are *not* equal.
    fn is_not_equal(&self, other: &Self) -> Self::Output {
        !self.is_equal(other)
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: u64 = 100;

    /// Returns a randomly-generated record that is not well-formed.
    fn sample_random_record(mode: Mode) -> Record<Circuit> {
        let rng = &mut test_rng();

        Record::<Circuit> {
            owner: Field::new(mode, UniformRand::rand(rng)),
            balance: Field::new(mode, UniformRand::rand(rng)),
            data: Field::new(mode, UniformRand::rand(rng)),
            nonce: Group::new(mode, UniformRand::rand(rng)),
            mac: Field::new(mode, UniformRand::rand(rng)),
            bcm: Group::new(mode, UniformRand::rand(rng)),
        }
    }

    fn check_is_equal(
        mode_a: Mode,
        mode_b: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) {
        for i in 0..ITERATIONS {
            // Sample two random records.
            let a = sample_random_record(mode_a);
            let b = sample_random_record(mode_b);

            Circuit::scope(&format!("{mode_a} {mode_a} {i}"), || {
                let equals = a.is_equal(&a);
                assert!(equals.eject_value());
            });

            Circuit::scope(&format!("{mode_a} {mode_b} {i}"), || {
                let equals = a.is_equal(&b);
                assert!(!equals.eject_value());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
        }
    }

    fn check_is_not_equal(
        mode_a: Mode,
        mode_b: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) {
        for i in 0..ITERATIONS {
            // Sample two random records.
            let a = sample_random_record(mode_a);
            let b = sample_random_record(mode_b);

            Circuit::scope(&format!("{mode_a} {mode_a} {i}"), || {
                let equals = a.is_not_equal(&a);
                assert!(!equals.eject_value());
            });

            Circuit::scope(&format!("{mode_a} {mode_b} {i}"), || {
                let equals = a.is_not_equal(&b);
                assert!(equals.eject_value());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
        }
    }

    #[test]
    fn test_is_equal_constant() {
        check_is_equal(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_is_equal() {
        check_is_equal(Mode::Constant, Mode::Public, 0, 0, 23, 31);
        check_is_equal(Mode::Constant, Mode::Private, 0, 0, 23, 31);
        check_is_equal(Mode::Public, Mode::Constant, 0, 0, 23, 31);
        check_is_equal(Mode::Private, Mode::Constant, 0, 0, 23, 31);
        check_is_equal(Mode::Public, Mode::Public, 0, 0, 23, 31);
        check_is_equal(Mode::Public, Mode::Private, 0, 0, 23, 31);
        check_is_equal(Mode::Private, Mode::Public, 0, 0, 23, 31);
        check_is_equal(Mode::Private, Mode::Private, 0, 0, 23, 31);
    }

    #[test]
    fn test_is_not_equal_constant() {
        check_is_not_equal(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_is_not_equal() {
        check_is_not_equal(Mode::Constant, Mode::Public, 0, 0, 23, 31);
        check_is_not_equal(Mode::Constant, Mode::Private, 0, 0, 23, 31);
        check_is_not_equal(Mode::Public, Mode::Constant, 0, 0, 23, 31);
        check_is_not_equal(Mode::Private, Mode::Constant, 0, 0, 23, 31);
        check_is_not_equal(Mode::Public, Mode::Public, 0, 0, 23, 31);
        check_is_not_equal(Mode::Public, Mode::Private, 0, 0, 23, 31);
        check_is_not_equal(Mode::Private, Mode::Public, 0, 0, 23, 31);
        check_is_not_equal(Mode::Private, Mode::Private, 0, 0, 23, 31);
    }
}
