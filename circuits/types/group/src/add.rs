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

impl<E: Environment> Add<Self> for Group<E> {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        self + &other
    }
}

impl<E: Environment> Add<&Self> for Group<E> {
    type Output = Self;

    fn add(self, other: &Self) -> Self::Output {
        // This swap reduces the number of constants by one.
        let (this, that) = match other.is_constant() {
            true => (&self, other),
            false => (other, &self),
        };

        let a = Field::constant(E::AffineParameters::COEFF_A);
        let d = Field::constant(E::AffineParameters::COEFF_D);

        // Compute U = (-A * x1 + y1) * (x2 + y2)
        let u1 = (&this.x * &-&a) + &this.y;
        let u2 = &that.x + &that.y;
        let u = u1 * u2;

        // Compute v0 = x1 * y2
        let v0 = &this.x * &that.y;

        // Compute v1 = x2 * y1
        let v1 = &that.x * &this.y;

        // Compute v2 = d * v0 * v1
        let v2 = (&v0 * &v1) * d;

        // Compute x3 and y3.
        let (x3, y3) = witness!(|a, u, v0, v1, v2| {
            // Assign x3 = (v0 + v1) / (v2 + 1).
            let x3 = (v0 + v1) / (v2 + E::BaseField::one());
            // Assign y3 = (U + a * v0 - v1) / (1 - v2).
            let y3 = (u + (v0 * a) - v1) / (E::BaseField::one() - v2);
            // Return (x3, y3).
            (x3, y3)
        });

        // Ensure x3 is well-formed.
        // x3 * (v2 + 1) = v0 + v1
        let v2_plus_one = &v2 + &Field::one();
        let v0_plus_v1 = &v0 + &v1;
        E::enforce(|| (&x3, v2_plus_one, v0_plus_v1));

        // Ensure y3 is well-formed.
        // y3 * (1 - v2) = u + (a * v0) - v1
        let one_minus_v2 = Field::one() - v2;
        let a_v0 = v0 * a;
        let u_plus_a_v0_minus_v1 = u + a_v0 - v1;
        E::enforce(|| (&y3, one_minus_v2, u_plus_a_v0_minus_v1));

        Self { x: x3, y: y3 }
    }
}

impl<E: Environment> Add<&Group<E>> for &Group<E> {
    type Output = Group<E>;

    fn add(self, other: &Group<E>) -> Self::Output {
        (*self).clone() + other
    }
}

impl<E: Environment> AddAssign<Self> for Group<E> {
    fn add_assign(&mut self, other: Self) {
        *self += &other;
    }
}

impl<E: Environment> AddAssign<&Self> for Group<E> {
    fn add_assign(&mut self, other: &Self) {
        *self = self.clone() + other;
    }
}

impl<E: Environment> Count<dyn Add<Group<E>, Output = Group<E>>> for Group<E> {
    type Case = (Mode, Mode);

    fn count(input: &Self::Case) -> CircuitCount {
        match (input.0, input.1) {
            (Mode::Constant, Mode::Constant) => CircuitCount::exact(4, 0, 0, 0),
            (Mode::Constant, _) | (_, Mode::Constant) => CircuitCount::exact(2, 0, 3, 3),
            (_, _) => CircuitCount::exact(2, 0, 6, 6),
        }
    }
}

impl<E: Environment> OutputMode<dyn Add<Group<E>, Output = Group<E>>> for Group<E> {
    type Case = (Mode, Mode);

    fn output_mode(input: &Self::Case) -> Mode {
        match (input.0, input.1) {
            (Mode::Constant, Mode::Constant) => Mode::Constant,
            (_, _) => Mode::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::{assert_count, assert_output_mode, Circuit};
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: usize = 100;

    fn check_add(name: &str, expected: &<Circuit as Environment>::Affine, a: &Group<Circuit>, b: &Group<Circuit>) {
        Circuit::scope(name, || {
            let candidate = a + b;
            assert_eq!(*expected, candidate.eject_value(), "({} + {})", a.eject_value(), b.eject_value());
            assert_count!(
                Group<Circuit>,
                Add<Group<Circuit>, Output = Group<Circuit>>,
                &(a.eject_mode(), b.eject_mode())
            );
            assert_output_mode!(
                candidate,
                Group<Circuit>,
                Add<Group<Circuit>, Output = Group<Circuit>>,
                &(a.eject_mode(), b.eject_mode())
            );
        });
    }

    fn check_add_assign(
        name: &str,
        expected: &<Circuit as Environment>::Affine,
        a: &Group<Circuit>,
        b: &Group<Circuit>,
    ) {
        Circuit::scope(name, || {
            let mut candidate = a.clone();
            candidate += b;
            assert_eq!(*expected, candidate.eject_value(), "({} + {})", a.eject_value(), b.eject_value());
            assert_count!(
                Group<Circuit>,
                Add<Group<Circuit>, Output = Group<Circuit>>,
                &(a.eject_mode(), b.eject_mode())
            );
            assert_output_mode!(
                candidate,
                Group<Circuit>,
                Add<Group<Circuit>, Output = Group<Circuit>>,
                &(a.eject_mode(), b.eject_mode())
            );
        });
    }

    #[test]
    fn test_constant_plus_constant() {
        for i in 0..ITERATIONS {
            let first = <Circuit as Environment>::Affine::rand(&mut test_rng());
            let second = <Circuit as Environment>::Affine::rand(&mut test_rng());

            let expected = (first.to_projective() + second.to_projective()).into();
            let a = Group::<Circuit>::new(Mode::Constant, first);
            let b = Group::<Circuit>::new(Mode::Constant, second);

            let name = format!("Add: a + b {}", i);
            check_add(&name, &expected, &a, &b);
            let name = format!("AddAssign: a + b {}", i);
            check_add_assign(&name, &expected, &a, &b);
        }
    }

    #[test]
    fn test_constant_plus_public() {
        for i in 0..ITERATIONS {
            let first = <Circuit as Environment>::Affine::rand(&mut test_rng());
            let second = <Circuit as Environment>::Affine::rand(&mut test_rng());

            let expected = (first.to_projective() + second.to_projective()).into();
            let a = Group::<Circuit>::new(Mode::Constant, first);
            let b = Group::<Circuit>::new(Mode::Public, second);

            let name = format!("Add: a + b {}", i);
            check_add(&name, &expected, &a, &b);
            let name = format!("AddAssign: a + b {}", i);
            check_add_assign(&name, &expected, &a, &b);
        }
    }

    #[test]
    fn test_public_plus_constant() {
        for i in 0..ITERATIONS {
            let first = <Circuit as Environment>::Affine::rand(&mut test_rng());
            let second = <Circuit as Environment>::Affine::rand(&mut test_rng());

            let expected = (first.to_projective() + second.to_projective()).into();
            let a = Group::<Circuit>::new(Mode::Public, first);
            let b = Group::<Circuit>::new(Mode::Constant, second);

            let name = format!("Add: a + b {}", i);
            check_add(&name, &expected, &a, &b);
            let name = format!("AddAssign: a + b {}", i);
            check_add_assign(&name, &expected, &a, &b);
        }
    }

    #[test]
    fn test_constant_plus_private() {
        for i in 0..ITERATIONS {
            let first = <Circuit as Environment>::Affine::rand(&mut test_rng());
            let second = <Circuit as Environment>::Affine::rand(&mut test_rng());

            let expected = (first.to_projective() + second.to_projective()).into();
            let a = Group::<Circuit>::new(Mode::Constant, first);
            let b = Group::<Circuit>::new(Mode::Private, second);

            let name = format!("Add: a + b {}", i);
            check_add(&name, &expected, &a, &b);
            let name = format!("AddAssign: a + b {}", i);
            check_add_assign(&name, &expected, &a, &b);
        }
    }

    #[test]
    fn test_private_plus_constant() {
        for i in 0..ITERATIONS {
            let first = <Circuit as Environment>::Affine::rand(&mut test_rng());
            let second = <Circuit as Environment>::Affine::rand(&mut test_rng());

            let expected = (first.to_projective() + second.to_projective()).into();
            let a = Group::<Circuit>::new(Mode::Private, first);
            let b = Group::<Circuit>::new(Mode::Constant, second);

            let name = format!("Add: a + b {}", i);
            check_add(&name, &expected, &a, &b);
            let name = format!("AddAssign: a + b {}", i);
            check_add_assign(&name, &expected, &a, &b);
        }
    }

    #[test]
    fn test_public_plus_public() {
        for i in 0..ITERATIONS {
            let first = <Circuit as Environment>::Affine::rand(&mut test_rng());
            let second = <Circuit as Environment>::Affine::rand(&mut test_rng());

            let expected = (first.to_projective() + second.to_projective()).into();
            let a = Group::<Circuit>::new(Mode::Public, first);
            let b = Group::<Circuit>::new(Mode::Public, second);

            let name = format!("Add: a + b {}", i);
            check_add(&name, &expected, &a, &b);
            let name = format!("AddAssign: a + b {}", i);
            check_add_assign(&name, &expected, &a, &b);
        }
    }

    #[test]
    fn test_public_plus_private() {
        for i in 0..ITERATIONS {
            let first = <Circuit as Environment>::Affine::rand(&mut test_rng());
            let second = <Circuit as Environment>::Affine::rand(&mut test_rng());

            let expected = (first.to_projective() + second.to_projective()).into();
            let a = Group::<Circuit>::new(Mode::Public, first);
            let b = Group::<Circuit>::new(Mode::Private, second);

            let name = format!("Add: a + b {}", i);
            check_add(&name, &expected, &a, &b);
            let name = format!("AddAssign: a + b {}", i);
            check_add_assign(&name, &expected, &a, &b);
        }
    }

    #[test]
    fn test_private_plus_public() {
        for i in 0..ITERATIONS {
            let first = <Circuit as Environment>::Affine::rand(&mut test_rng());
            let second = <Circuit as Environment>::Affine::rand(&mut test_rng());

            let expected = (first.to_projective() + second.to_projective()).into();
            let a = Group::<Circuit>::new(Mode::Private, first);
            let b = Group::<Circuit>::new(Mode::Public, second);

            let name = format!("Add: a + b {}", i);
            check_add(&name, &expected, &a, &b);
            let name = format!("AddAssign: a + b {}", i);
            check_add_assign(&name, &expected, &a, &b);
        }
    }

    #[test]
    fn test_private_plus_private() {
        for i in 0..ITERATIONS {
            let first = <Circuit as Environment>::Affine::rand(&mut test_rng());
            let second = <Circuit as Environment>::Affine::rand(&mut test_rng());

            let expected = (first.to_projective() + second.to_projective()).into();
            let a = Group::<Circuit>::new(Mode::Private, first);
            let b = Group::<Circuit>::new(Mode::Private, second);

            let name = format!("Add: a + b {}", i);
            check_add(&name, &expected, &a, &b);
            let name = format!("AddAssign: a + b {}", i);
            check_add_assign(&name, &expected, &a, &b);
        }
    }

    #[test]
    fn test_add_matches() {
        // Sample two random elements.
        let a = <Circuit as Environment>::Affine::rand(&mut test_rng());
        let b = <Circuit as Environment>::Affine::rand(&mut test_rng());
        let expected: <Circuit as Environment>::Affine = (a.to_projective() + b.to_projective()).into();

        // Constant
        let first = Group::<Circuit>::new(Mode::Constant, a);
        let second = Group::<Circuit>::new(Mode::Constant, b);
        let candidate_a = first + second;
        assert_eq!(expected, candidate_a.eject_value());

        // Private
        let first = Group::<Circuit>::new(Mode::Private, a);
        let second = Group::<Circuit>::new(Mode::Private, b);
        let candidate_b = first + second;
        assert_eq!(expected, candidate_b.eject_value());
    }
}
