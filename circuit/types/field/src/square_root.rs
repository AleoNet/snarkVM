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

    fn square_root(&self) -> Self::Output {
        let square_root = witness!(|self| match self.square_root() {
            Ok(square_root) => square_root,
            _ => console::Field::zero(),
        });

        // Ensure `square_root` * `square_root` == `self`.
        E::enforce(|| (&square_root, &square_root, self));

        square_root
    }
}

impl<E: Environment> Metrics<dyn SquareRoot<Output = Field<E>>> for Field<E> {
    type Case = Mode;

    fn count(case: &Self::Case) -> Count {
        match case.is_constant() {
            true => Count::is(1, 0, 0, 0),
            false => Count::is(0, 0, 1, 1),
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

    #[test]
    fn test_square_root() {
        let mut rng = TestRng::default();

        check_square_root("Constant", Mode::Constant, &mut rng);
        check_square_root("Public", Mode::Public, &mut rng);
        check_square_root("Private", Mode::Private, &mut rng);
    }
}
