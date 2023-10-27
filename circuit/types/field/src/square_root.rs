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
            // Compute it's square root, or skip this iteration if it does not natively exist.
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
            // Compute it's square root, or skip this iteration if it does not natively exist.
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
}
