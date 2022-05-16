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

impl<E: Environment> Double for Group<E> {
    type Output = Group<E>;

    fn double(self) -> Self::Output {
        (&self).double()
    }
}

impl<E: Environment> Double for &Group<E> {
    type Output = Group<E>;

    fn double(self) -> Self::Output {
        // If `self` is constant *and* `self` is zero, then return `self`.
        if self.is_constant() && self.eject_value().is_zero() {
            self.clone()
        }
        // Otherwise, compute `self` + `self`.
        else {
            let a = Field::constant(E::AffineParameters::COEFF_A);
            let two = Field::one().double();

            // Compute xy, xx, yy, axx.
            let xy = &self.x * &self.y;
            let x2 = self.x.square();
            let y2 = self.y.square();
            let ax2 = &x2 * &a;

            // Compute x3 and y3.
            let (x3, y3) = witness!(|two, xy, y2, ax2| {
                // Assign x3 = (2xy) / (ax^2 + y^2).
                let x3 = xy.double() / (ax2 + y2);
                // Assign y3 = (y^2 - ax^2) / (2 - ax^2 - y^2).
                let y3 = (y2 - ax2) / (two - ax2 - y2);
                // Return (x3, y3).
                (x3, y3)
            });

            // Ensure x3 is well-formed.
            // x3 * (ax^2 + y^2) = 2xy
            let ax2_plus_y2 = &ax2 + &y2;
            let two_xy = xy.double();
            E::enforce(|| (&x3, &ax2_plus_y2, two_xy));

            // Ensure y3 is well-formed.
            // y3 * (2 - (ax^2 + y^2)) = y^2 - ax^2
            let y2_minus_a_x2 = y2 - ax2;
            let two_minus_ax2_minus_y2 = two - ax2_plus_y2;
            E::enforce(|| (&y3, two_minus_ax2_minus_y2, y2_minus_a_x2));

            Group { x: x3, y: y3 }
        }
    }
}

impl<E: Environment> Metadata<dyn Double<Output = Group<E>>> for Group<E> {
    type Case = CircuitType<Self>;
    type OutputType = CircuitType<Self>;

    fn count(case: &Self::Case) -> Count {
        match case {
            CircuitType::Constant(constant) => match constant.eject_value().is_zero() {
                true => Count::is(0, 0, 0, 0),
                false => Count::is(3, 0, 0, 0),
            },
            _ => Count::is(1, 0, 5, 5),
        }
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        match case {
            CircuitType::Constant(constant) => CircuitType::from(constant.circuit().double()),
            _ => CircuitType::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_curves::ProjectiveCurve;
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: u64 = 250;

    fn check_double(name: &str, expected: &<Circuit as Environment>::Affine, candidate: &Group<Circuit>) {
        Circuit::scope(name, || {
            let result = candidate.double();
            assert_eq!(*expected, result.eject_value());

            let case = CircuitType::from(candidate);
            assert_count!(Double(Group) => Group, &case);
            assert_output_type!(Double(Group) => Group, case, result);
        });
    }

    fn run_test(mode: Mode) {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let given: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());
            let candidate = Group::<Circuit>::new(mode, given);

            let name = format!("Double: {} {}", mode, i);
            check_double(&name, &given.to_projective().double().into(), &candidate)
        }

        // Test zero case.
        let given = <Circuit as Environment>::Affine::zero();
        let candidate = Group::<Circuit>::new(mode, given);

        let name = format!("Double Zero: {}", mode);
        check_double(&name, &given.to_projective().double().into(), &candidate);
    }

    #[test]
    fn test_double_constant() {
        run_test(Mode::Constant);
    }

    #[test]
    fn test_double_public() {
        run_test(Mode::Public);
    }

    #[test]
    fn test_double_private() {
        run_test(Mode::Private)
    }
}
