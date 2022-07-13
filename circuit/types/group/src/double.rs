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

    fn double(&self) -> Self::Output {
        // If `self` is constant *and* `self` is zero, then return `self`.
        if self.is_constant() && self.eject_value().is_zero() {
            self.clone()
        }
        // Otherwise, compute `self` + `self`.
        else {
            let a = Field::constant(console::Field::new(E::AffineParameters::COEFF_A));
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

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    const ITERATIONS: u64 = 250;

    #[test]
    fn test_double() {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let point: console::Group<<Circuit as Environment>::Network> = Uniform::rand(&mut test_rng());
            let expected = point.double();

            // Constant variable
            let affine = Group::<Circuit>::new(Mode::Constant, point);

            Circuit::scope(&format!("Constant {}", i), || {
                let candidate = affine.double();
                assert_eq!(expected, candidate.eject_value());
                assert_scope!(3, 0, 0, 0);
            });
            Circuit::reset();

            // Public variable
            let affine = Group::<Circuit>::new(Mode::Public, point);

            Circuit::scope(&format!("Public {}", i), || {
                let candidate = affine.double();
                assert_eq!(expected, candidate.eject_value());
                assert_scope!(1, 0, 5, 5);
            });
            Circuit::reset();

            // Private variable
            let affine = Group::<Circuit>::new(Mode::Private, point);

            Circuit::scope(&format!("Private {}", i), || {
                let candidate = affine.double();
                assert_eq!(expected, candidate.eject_value());
                assert_scope!(1, 0, 5, 5);
            });
            Circuit::reset();
        }
    }

    #[test]
    fn test_double_matches() {
        // Sample two random elements.
        let a = Uniform::rand(&mut test_rng());
        let expected = a + a;

        // Constant
        let candidate_a = Group::<Circuit>::new(Mode::Constant, a).double();
        assert_eq!(expected, candidate_a.eject_value());

        // Private
        let candidate_b = Group::<Circuit>::new(Mode::Private, a).double();
        assert_eq!(expected, candidate_b.eject_value());
    }
}
