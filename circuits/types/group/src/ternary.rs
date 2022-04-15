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
use snarkvm_circuits_environment::CircuitOrMode;

impl<E: Environment> Ternary for Group<E> {
    type Boolean = Boolean<E>;
    type Output = Group<E>;

    /// Returns `first` if `condition` is `true`, otherwise returns `second`.
    fn ternary(condition: &Self::Boolean, first: &Self, second: &Self) -> Self::Output {
        let x = Ternary::ternary(condition, &first.x, &second.x);
        let y = Ternary::ternary(condition, &first.y, &second.y);
        Group { x, y }
    }
}

impl<E: Environment> Count<dyn Ternary<Boolean = Boolean<E>, Output = Group<E>>> for Group<E> {
    type Case = (Mode, Mode, Mode);

    fn count(parameter: &Self::Case) -> CircuitCount {
        match parameter {
            (Mode::Constant, _, _)
            | (Mode::Public, Mode::Constant, Mode::Constant)
            | (Mode::Private, Mode::Constant, Mode::Constant) => CircuitCount::exact(0, 0, 0, 0),
            _ => CircuitCount::exact(0, 0, 2, 2),
        }
    }
}

impl<E: Environment> OutputMode<dyn Ternary<Boolean = Boolean<E>, Output = Self>> for Group<E> {
    type Case = (CircuitOrMode<Boolean<E>>, Mode, Mode);

    fn output_mode(parameter: &Self::Case) -> Mode {
        match parameter.0.is_constant() {
            false => Mode::Private,
            true => match &parameter.0 {
                CircuitOrMode::Mode(..) => E::halt("Circuit is required to determine output mode."),
                CircuitOrMode::Circuit(circuit) => match circuit.eject_value() {
                    true => parameter.1,
                    false => parameter.2,
                },
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    fn check_ternary(
        name: &str,
        expected: <Circuit as Environment>::Affine,
        condition: Boolean<Circuit>,
        a: Group<Circuit>,
        b: Group<Circuit>,
    ) {
        Circuit::scope(name, || {
            let case = format!("({} ? {} : {})", condition.eject_value(), a.eject_value(), b.eject_value());
            let candidate = Group::ternary(&condition, &a, &b);
            assert_eq!(expected, candidate.eject_value(), "{case}");
            assert_count!(
                Group<Circuit>,
                Ternary<Boolean = Boolean<Circuit>, Output = Group<Circuit>>,
                &(condition.eject_mode(), a.eject_mode(), b.eject_mode())
            );
            assert_output_mode!(
                candidate,
                Group<Circuit>,
                Ternary<Boolean = Boolean<Circuit>, Output = Group<Circuit>>,
                &(CircuitOrMode::Circuit(condition), a.eject_mode(), b.eject_mode())
            );
        });
    }

    #[test]
    fn test_constant_condition() {
        let first: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());
        let second: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());

        // false ? Constant : Constant
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Constant, false);
        let a = Group::<Circuit>::new(Mode::Constant, first);
        let b = Group::<Circuit>::new(Mode::Constant, second);
        check_ternary("false ? Constant : Constant", expected, condition, a, b);

        // false ? Constant : Public
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Constant, false);
        let a = Group::<Circuit>::new(Mode::Constant, first);
        let b = Group::<Circuit>::new(Mode::Public, second);
        check_ternary("false ? Constant : Public", expected, condition, a, b);

        // false ? Public : Constant
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Constant, false);
        let a = Group::<Circuit>::new(Mode::Public, first);
        let b = Group::<Circuit>::new(Mode::Constant, second);
        check_ternary("false ? Public : Constant", expected, condition, a, b);

        // false ? Public : Public
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Constant, false);
        let a = Group::<Circuit>::new(Mode::Public, first);
        let b = Group::<Circuit>::new(Mode::Public, second);
        check_ternary("false ? Public : Public", expected, condition, a, b);

        // false ? Public : Private
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Constant, false);
        let a = Group::<Circuit>::new(Mode::Public, first);
        let b = Group::<Circuit>::new(Mode::Private, second);
        check_ternary("false ? Public : Private", expected, condition, a, b);

        // false ? Private : Private
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Constant, false);
        let a = Group::<Circuit>::new(Mode::Private, first);
        let b = Group::<Circuit>::new(Mode::Private, second);
        check_ternary("false ? Private : Private", expected, condition, a, b);

        // true ? Constant : Constant
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Constant, true);
        let a = Group::<Circuit>::new(Mode::Constant, first);
        let b = Group::<Circuit>::new(Mode::Constant, second);
        check_ternary("true ? Constant : Constant", expected, condition, a, b);

        // true ? Constant : Public
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Constant, true);
        let a = Group::<Circuit>::new(Mode::Constant, first);
        let b = Group::<Circuit>::new(Mode::Public, second);
        check_ternary("true ? Constant : Public", expected, condition, a, b);

        // true ? Public : Constant
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Constant, true);
        let a = Group::<Circuit>::new(Mode::Public, first);
        let b = Group::<Circuit>::new(Mode::Constant, second);
        check_ternary("true ? Public : Constant", expected, condition, a, b);

        // true ? Public : Public
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Constant, true);
        let a = Group::<Circuit>::new(Mode::Public, first);
        let b = Group::<Circuit>::new(Mode::Public, second);
        check_ternary("true ? Public : Public", expected, condition, a, b);

        // true ? Public : Private
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Constant, true);
        let a = Group::<Circuit>::new(Mode::Public, first);
        let b = Group::<Circuit>::new(Mode::Private, second);
        check_ternary("true ? Public : Private", expected, condition, a, b);

        // true ? Private : Private
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Constant, true);
        let a = Group::<Circuit>::new(Mode::Private, first);
        let b = Group::<Circuit>::new(Mode::Private, second);
        check_ternary("true ? Private : Private", expected, condition, a, b);
    }

    #[test]
    fn test_public_condition_and_constant_inputs() {
        let first: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());
        let second: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());

        // false ? Constant : Constant
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Public, false);
        let a = Group::<Circuit>::new(Mode::Constant, first);
        let b = Group::<Circuit>::new(Mode::Constant, second);
        check_ternary("false ? Constant : Constant", expected, condition, a, b);

        // true ? Constant : Constant
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Public, true);
        let a = Group::<Circuit>::new(Mode::Constant, first);
        let b = Group::<Circuit>::new(Mode::Constant, second);
        check_ternary("true ? Constant : Constant", expected, condition, a, b);
    }

    #[test]
    fn test_public_condition_and_mixed_inputs() {
        let first: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());
        let second: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());

        // false ? Constant : Public
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Public, false);
        let a = Group::<Circuit>::new(Mode::Constant, first);
        let b = Group::<Circuit>::new(Mode::Public, second);
        check_ternary("false ? Constant : Public", expected, condition, a, b);

        // false ? Public : Constant
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Public, false);
        let a = Group::<Circuit>::new(Mode::Public, first);
        let b = Group::<Circuit>::new(Mode::Constant, second);
        check_ternary("false ? Public : Constant", expected, condition, a, b);

        // true ? Constant : Public
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Public, true);
        let a = Group::<Circuit>::new(Mode::Constant, first);
        let b = Group::<Circuit>::new(Mode::Public, second);
        check_ternary("true ? Constant : Public", expected, condition, a, b);

        // true ? Public : Constant
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Public, true);
        let a = Group::<Circuit>::new(Mode::Public, first);
        let b = Group::<Circuit>::new(Mode::Constant, second);
        check_ternary("true ? Public : Constant", expected, condition, a, b);
    }

    #[test]
    fn test_private_condition_and_constant_inputs() {
        let first: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());
        let second: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());

        // false ? Constant : Constant
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Private, false);
        let a = Group::<Circuit>::new(Mode::Constant, first);
        let b = Group::<Circuit>::new(Mode::Constant, second);
        check_ternary("false ? Constant : Constant", expected, condition, a, b);

        // true ? Constant : Constant
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Private, true);
        let a = Group::<Circuit>::new(Mode::Constant, first);
        let b = Group::<Circuit>::new(Mode::Constant, second);
        check_ternary("true ? Constant : Constant", expected, condition, a, b);
    }

    #[test]
    fn test_private_condition_and_mixed_inputs() {
        let first: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());
        let second: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());

        // false ? Constant : Public
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Private, false);
        let a = Group::<Circuit>::new(Mode::Constant, first);
        let b = Group::<Circuit>::new(Mode::Public, second);
        check_ternary("false ? Constant : Public", expected, condition, a, b);

        // false ? Public : Constant
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Private, false);
        let a = Group::<Circuit>::new(Mode::Public, first);
        let b = Group::<Circuit>::new(Mode::Constant, second);
        check_ternary("false ? Public : Constant", expected, condition, a, b);

        // true ? Constant : Public
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Private, true);
        let a = Group::<Circuit>::new(Mode::Constant, first);
        let b = Group::<Circuit>::new(Mode::Public, second);
        check_ternary("true ? Constant : Public", expected, condition, a, b);

        // true ? Public : Constant
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Private, true);
        let a = Group::<Circuit>::new(Mode::Public, first);
        let b = Group::<Circuit>::new(Mode::Constant, second);
        check_ternary("true ? Public : Constant", expected, condition, a, b);
    }

    #[test]
    fn test_public_condition_and_variable_inputs() {
        let first: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());
        let second: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());

        // false ? Public : Public
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Public, false);
        let a = Group::<Circuit>::new(Mode::Public, first);
        let b = Group::<Circuit>::new(Mode::Public, second);
        check_ternary("false ? Public : Public", expected, condition, a, b);

        // false ? Public : Private
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Public, false);
        let a = Group::<Circuit>::new(Mode::Public, first);
        let b = Group::<Circuit>::new(Mode::Private, second);
        check_ternary("false ? Public : Private", expected, condition, a, b);

        // false ? Private : Public
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Public, false);
        let a = Group::<Circuit>::new(Mode::Private, first);
        let b = Group::<Circuit>::new(Mode::Public, second);
        check_ternary("false ? Private : Public", expected, condition, a, b);

        // false ? Private : Private
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Public, false);
        let a = Group::<Circuit>::new(Mode::Private, first);
        let b = Group::<Circuit>::new(Mode::Private, second);
        check_ternary("false ? Private : Private", expected, condition, a, b);

        // true ? Public : Public
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Public, true);
        let a = Group::<Circuit>::new(Mode::Public, first);
        let b = Group::<Circuit>::new(Mode::Public, second);
        check_ternary("true ? Public : Public", expected, condition, a, b);

        // true ? Public : Private
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Public, true);
        let a = Group::<Circuit>::new(Mode::Public, first);
        let b = Group::<Circuit>::new(Mode::Private, second);
        check_ternary("true ? Public : Private", expected, condition, a, b);

        // true ? Private : Public
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Public, true);
        let a = Group::<Circuit>::new(Mode::Private, first);
        let b = Group::<Circuit>::new(Mode::Public, second);
        check_ternary("true ? Private : Public", expected, condition, a, b);

        // true ? Private : Private
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Public, true);
        let a = Group::<Circuit>::new(Mode::Private, first);
        let b = Group::<Circuit>::new(Mode::Private, second);
        check_ternary("true ? Private : Private", expected, condition, a, b);
    }

    #[test]
    fn test_private_condition_and_variable_inputs() {
        let first: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());
        let second: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());

        // false ? Public : Public
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Private, false);
        let a = Group::<Circuit>::new(Mode::Public, first);
        let b = Group::<Circuit>::new(Mode::Public, second);
        check_ternary("false ? Public : Public", expected, condition, a, b);

        // false ? Public : Private
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Private, false);
        let a = Group::<Circuit>::new(Mode::Public, first);
        let b = Group::<Circuit>::new(Mode::Private, second);
        check_ternary("false ? Public : Private", expected, condition, a, b);

        // false ? Private : Public
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Private, false);
        let a = Group::<Circuit>::new(Mode::Private, first);
        let b = Group::<Circuit>::new(Mode::Public, second);
        check_ternary("false ? Private : Public", expected, condition, a, b);

        // false ? Private : Private
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Private, false);
        let a = Group::<Circuit>::new(Mode::Private, first);
        let b = Group::<Circuit>::new(Mode::Private, second);
        check_ternary("false ? Private : Private", expected, condition, a, b);

        // true ? Public : Public
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Private, true);
        let a = Group::<Circuit>::new(Mode::Public, first);
        let b = Group::<Circuit>::new(Mode::Public, second);
        check_ternary("true ? Public : Public", expected, condition, a, b);

        // true ? Public : Private
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Private, true);
        let a = Group::<Circuit>::new(Mode::Public, first);
        let b = Group::<Circuit>::new(Mode::Private, second);
        check_ternary("true ? Public : Private", expected, condition, a, b);

        // true ? Private : Public
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Private, true);
        let a = Group::<Circuit>::new(Mode::Private, first);
        let b = Group::<Circuit>::new(Mode::Public, second);
        check_ternary("true ? Private : Public", expected, condition, a, b);

        // true ? Private : Private
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Private, true);
        let a = Group::<Circuit>::new(Mode::Private, first);
        let b = Group::<Circuit>::new(Mode::Private, second);
        check_ternary("true ? Private : Private", expected, condition, a, b);
    }
}
