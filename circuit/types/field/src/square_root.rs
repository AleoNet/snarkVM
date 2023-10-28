// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;

impl<E: Environment> SquareRoot for Field<E> {
    type Output = Self;

    /// Returns the square root of `self`.
    /// If there are two square roots, the bitwise lesser one is returned.
    /// If there are no square roots, zero is returned.
    fn square_root(&self) -> Self::Output {
        let square_root: Field<E> = witness!(|self| match self.square_root() {
            Ok(square_root) => square_root,
            _ => console::Field::zero(),
        });

        // Ensure `square_root` * `square_root` == `self`.
        E::enforce(|| (&square_root, &square_root, self));

        // Define the MODULUS_MINUS_ONE_DIV_TWO as a constant.
        let modulus_minus_one_div_two = match E::BaseField::from_bigint(E::BaseField::modulus_minus_one_div_two()) {
            Some(modulus_minus_one_div_two) => Field::constant(console::Field::new(modulus_minus_one_div_two)),
            None => E::halt("Failed to initialize MODULUS_MINUS_ONE_DIV_TWO as a constant"),
        };

        // Ensure that `square_root` is less than or equal to (MODULUS - 1) / 2.
        // This ensures that the resulting square root is unique.
        let is_less_than_or_equal = square_root.is_less_than_or_equal(&modulus_minus_one_div_two);
        E::assert(is_less_than_or_equal);

        square_root
    }
}

impl<E: Environment> Field<E> {
    /// Returns the square root of `self`, where the least significant bit of the square root is zero.
    pub fn even_square_root(&self) -> Self {
        let square_root: Field<E> = witness!(|self| match self.even_square_root() {
            Ok(square_root) => square_root,
            _ => console::Field::zero(),
        });

        // Ensure `square_root` * `square_root` == `self`.
        E::enforce(|| (&square_root, &square_root, self));

        // Ensure that the LSB of the square root is zero.
        // Note that this unwrap is safe since the number of bits is always greater than zero.
        E::assert(!square_root.to_bits_be().last().unwrap());

        square_root
    }
}

impl<E: Environment> Field<E> {
    /// Returns both square roots of `self` (hence the plural 'roots' in the name of the function),
    /// along with a boolean error flag, which is set iff `self` is not a square.
    ///
    /// In the console computation:
    /// if `self` is a non-zero square,
    /// the first field result is the positive root (i.e. closer to 0)
    /// and the second field result is the negative root (i.e. closer to the prime);
    /// if `self` is 0, both field results are 0;
    /// if `self` is not a square, both field results are 0, but immaterial.
    ///
    /// The 'nondeterministic' part of the function name refers to the synthesized circuit,
    /// whose represented computation, unlike the console computation just described,
    /// returns the two roots (if `self` is a non-zero square) in no specified order.
    /// This nondeterminism saves constraints, but generally this circuit should be only used
    /// as part of larger circuits for which the nondeterminism in the order of the two roots does not matter,
    /// and where the larger circuits represent deterministic computations despite this internal nondeterminism.
    pub fn square_roots_flagged_nondeterministic(&self) -> (Boolean<E>, Self, Self) {
        // Obtain (p-1)/2, as a constant field element.
        let modulus_minus_one_div_two = match E::BaseField::from_bigint(E::BaseField::modulus_minus_one_div_two()) {
            Some(modulus_minus_one_div_two) => Field::constant(console::Field::new(modulus_minus_one_div_two)),
            None => E::halt("Failed to initialize (modulus - 1) / 2"),
        };

        // Use Euler's criterion: self is a non-zero square iff self^((p-1)/2) is 1.
        let euler = self.pow(modulus_minus_one_div_two);
        let is_nonzero_square = euler.is_equal(&Field::one());

        // Calculate the witness for the first square result.
        // The called function square_root returns the square root closer to 0.
        let root_witness = match self.eject_value().square_root() {
            Ok(root) => root,
            Err(_) => console::Field::zero(),
        };

        // In order to avoid actually calculating the square root in the circuit,
        // we would like to generate a constraint saying that squaring the root yields self.
        // But this constraint would have no solutions if self is not a square.
        // So we introduce a new variable that is either self (if square) or 0 (otherwise):
        // either way, this new variable is a square.
        let square = Self::ternary(&is_nonzero_square, self, &Field::zero());

        // We introduce a variable for the first root we return,
        // and constrain it to yield, when squared, the square introduced just above.
        // Thus, if self is a square this is a square root of self; otherwise it is 0, because only 0 yields 0 when squared.
        // The variable is actually a constant if self is constant, otherwise it is private (even if self is public).
        let mode = if self.eject_mode() == Mode::Constant { Mode::Constant } else { Mode::Private };
        let first_root = Field::new(mode, root_witness);
        E::enforce(|| (&first_root, &first_root, &square));

        // The second root returned by this function is the negation of the first one.
        // So if self is a non-zero square, this is always different from the first root,
        // but in the circuit it can be either positive (and the other negative) or vice versa.
        let second_root = first_root.clone().neg();

        // The error flag is set iff self is a non-square, i.e. it is neither zero nor a non-zero square.
        let is_nonzero = self.is_not_equal(&Field::zero());
        let error_flag = is_nonzero.bitand(is_nonzero_square.not());

        (error_flag, first_root, second_root)
    }
}

impl<E: Environment> Metrics<dyn SquareRoot<Output = Field<E>>> for Field<E> {
    type Case = Mode;

    fn count(case: &Self::Case) -> Count {
        match case.is_constant() {
            true => Count::is(2, 0, 0, 0),
            false => Count::is(1, 0, 758, 761),
        }
    }
}

impl<E: Environment> OutputMode<dyn SquareRoot<Output = Field<E>>> for Field<E> {
    type Case = Mode;

    fn output_mode(case: &Self::Case) -> Mode {
        match case.is_constant() {
            true => Mode::Constant,
            false => Mode::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    const ITERATIONS: u64 = 1_000;

    fn check_square_root(name: &str, mode: Mode, rng: &mut TestRng) {
        for _ in 0..ITERATIONS {
            // Sample a random element.
            let given: console::Field<<Circuit as Environment>::Network> = Uniform::rand(rng);
            // Compute its square root, or skip this iteration if it does not natively exist.
            if let Ok(expected) = given.square_root() {
                let input = Field::<Circuit>::new(mode, given);

                Circuit::scope(name, || {
                    let candidate = input.square_root();
                    assert_eq!(expected, candidate.eject_value());
                    assert_count!(SquareRoot(Field) => Field, &mode);
                    assert_output_mode!(SquareRoot(Field) => Field, &mode, candidate);
                });
                Circuit::reset();
            }
        }
    }

    fn check_even_square_root(
        name: &str,
        rng: &mut TestRng,
        mode: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) {
        for _ in 0..ITERATIONS {
            // Sample a random element.
            let given: console::Field<<Circuit as Environment>::Network> = Uniform::rand(rng);
            // Compute its square root, or skip this iteration if it does not natively exist.
            if let Ok(expected) = given.even_square_root() {
                let input = Field::<Circuit>::new(mode, given);

                Circuit::scope(name, || {
                    let candidate = input.even_square_root();
                    assert_eq!(expected, candidate.eject_value());
                    assert_scope!(num_constants, num_public, num_private, num_constraints);
                });
                Circuit::reset();
            }
        }
    }

    fn check_square_roots_flagged_nondeterministic(
        name: &str,
        mode: Mode,
        rng: &mut TestRng,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) {
        for _ in 0..ITERATIONS {
            // Sample a random element.
            let given: console::Field<<Circuit as Environment>::Network> = Uniform::rand(rng);
            // Compute square roots and error flag in console-land.
            let (expected_error_flag, expected_positive_root, expected_negative_root) = match given.square_root() {
                Ok(root) => (false, root, -root),
                Err(_) => (true, console::Field::zero(), console::Field::zero()),
            };
            // Compute square roots and error flag in circuit-land.
            let input = Field::<Circuit>::new(mode, given);
            Circuit::scope(name, || {
                let (candidate_error_flag, candidate_first_root, candidate_second_root) =
                    input.square_roots_flagged_nondeterministic();
                // Although the order of the roots is unspecified in the circuit,
                // the witness values are in a fixed order (first positive, then negative).
                assert_eq!(expected_error_flag, candidate_error_flag.eject_value());
                assert_eq!(expected_positive_root, candidate_first_root.eject_value());
                assert_eq!(expected_negative_root, candidate_second_root.eject_value());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
            Circuit::reset();
        }
    }

    #[test]
    fn test_square_root() {
        let mut rng = TestRng::default();

        check_square_root("Constant", Mode::Constant, &mut rng);
        check_square_root("Public", Mode::Public, &mut rng);
        check_square_root("Private", Mode::Private, &mut rng);
    }

    #[test]
    fn test_even_square_root() {
        let mut rng = TestRng::default();

        check_even_square_root("Constant", &mut rng, Mode::Constant, 254, 0, 0, 0);
        check_even_square_root("Public", &mut rng, Mode::Public, 0, 0, 506, 509);
        check_even_square_root("Private", &mut rng, Mode::Private, 0, 0, 506, 509);
    }

    #[test]
    fn test_square_roots_flagged_nondeterministic() {
        let mut rng = TestRng::default();

        check_square_roots_flagged_nondeterministic("Constant", Mode::Constant, &mut rng, 257, 0, 0, 0);
        check_square_roots_flagged_nondeterministic("Public", Mode::Public, &mut rng, 254, 0, 344, 344);
        check_square_roots_flagged_nondeterministic("Private", Mode::Private, &mut rng, 254, 0, 344, 344);
    }
}
