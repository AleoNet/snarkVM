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

    fn check_square_root(name: &str, mode: Mode) {
        for _ in 0..ITERATIONS {
            // Sample a random element.
            let given: console::Field<<Circuit as Environment>::Network> = Uniform::rand(&mut test_rng());
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
        check_square_root("Constant", Mode::Constant);
        check_square_root("Public", Mode::Public);
        check_square_root("Private", Mode::Private);
    }
}
