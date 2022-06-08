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

impl<E: Environment> One for Field<E> {
    type Boolean = Boolean<E>;

    fn one() -> Self {
        E::one().into()
    }

    fn is_one(&self) -> Self::Boolean {
        self.is_equal(&Field::one())
    }
}

impl<E: Environment> Metrics<dyn One<Boolean = Boolean<E>>> for Field<E> {
    type Case = ();

    fn count(_parameter: &Self::Case) -> Count {
        Count::is(0, 0, 0, 0)
    }
}

impl<E: Environment> OutputMode<dyn One<Boolean = Boolean<E>>> for Field<E> {
    type Case = ();

    fn output_mode(_input: &Self::Case) -> Mode {
        Mode::Constant
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    #[test]
    fn test_one() {
        let one = console::Field::<<Circuit as Environment>::Network>::one();

        Circuit::scope("One", || {
            assert_scope!(0, 0, 0, 0);
            let candidate = Field::<Circuit>::one();
            assert_eq!(one, candidate.eject_value());
            assert_count!(One<Boolean>() => Field, &());
            assert_output_mode!(One<Boolean>() => Field, &(), candidate);
        });
    }

    #[test]
    fn test_is_one() {
        let candidate = Field::<Circuit>::one();
        // Should equal 1.
        assert!(candidate.is_one().eject_value());
        // Should not equal 0.
        assert!(!candidate.is_zero().eject_value());
    }
}
