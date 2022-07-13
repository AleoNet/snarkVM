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

impl<E: Environment> FromBoolean for Field<E> {
    type Boolean = Boolean<E>;

    /// Initializes a base field from a boolean.
    fn from_boolean(boolean: &Self::Boolean) -> Self {
        Self::from((**boolean).clone())
    }
}

impl<E: Environment> Metrics<dyn FromBoolean<Boolean = Boolean<E>>> for Field<E> {
    type Case = ();

    fn count(_case: &Self::Case) -> Count {
        Count::is(0, 0, 0, 0)
    }
}

impl<E: Environment> OutputMode<dyn FromBoolean<Boolean = Boolean<E>>> for Field<E> {
    type Case = Mode;

    fn output_mode(case: &Self::Case) -> Mode {
        *case
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    fn check_from_boolean(mode: Mode) {
        for expected in &[true, false] {
            // Inject the boolean.
            let given = Boolean::<Circuit>::new(mode, *expected);

            Circuit::scope(format!("{mode} {expected}"), || {
                let candidate = Field::from_boolean(&given);
                match expected {
                    true => {
                        assert_eq!(console::Field::<<Circuit as Environment>::Network>::one(), candidate.eject_value())
                    }
                    false => {
                        assert_eq!(console::Field::<<Circuit as Environment>::Network>::zero(), candidate.eject_value())
                    }
                }
                assert_count!(FromBoolean(Boolean) => Field, &());
                assert_output_mode!(FromBoolean(Boolean) => Field, &mode, candidate);
            });
        }
    }

    #[test]
    fn test_from_boolean_constant() {
        check_from_boolean(Mode::Constant);
    }

    #[test]
    fn test_from_boolean_public() {
        check_from_boolean(Mode::Public);
    }

    #[test]
    fn test_from_boolean_private() {
        check_from_boolean(Mode::Private);
    }
}
