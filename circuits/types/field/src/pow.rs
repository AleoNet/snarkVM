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

#[allow(clippy::only_used_in_recursion)]
impl<E: Environment> Pow<Field<E>> for Field<E> {
    type Output = Field<E>;

    fn pow(self, exponent: Field<E>) -> Self::Output {
        self.pow(&exponent)
    }
}

impl<E: Environment> Pow<Field<E>> for &Field<E> {
    type Output = Field<E>;

    fn pow(self, exponent: Field<E>) -> Self::Output {
        self.pow(&exponent)
    }
}

impl<E: Environment> Pow<&Field<E>> for Field<E> {
    type Output = Field<E>;

    fn pow(self, exponent: &Field<E>) -> Self::Output {
        (&self).pow(exponent)
    }
}

impl<E: Environment> Pow<&Field<E>> for &Field<E> {
    type Output = Field<E>;

    fn pow(self, exponent: &Field<E>) -> Self::Output {
        // Initialize the output.
        let mut output = Field::one();

        // If the exponent is a constant, eject its bits to determine whether to multiply in each iteration.
        if exponent.is_constant() {
            for bit in exponent.to_bits_be() {
                // Square the output.
                output = output.square();
                // If `bit` is `true, set the output to `output * self`.
                if bit.eject_value() {
                    output *= self;
                }
            }
        }
        // If the exponent is a variable, use a ternary to select whether to multiply in each iteration.
        else {
            for bit in exponent.to_bits_be() {
                // Square the output.
                output = output.square();
                // If `bit` is `true, set the output to `output * self`.
                output = Field::ternary(&bit, &(&output * self), &output);
            }
        }

        output
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: usize = 10;

    fn check_pow(
        name: &str,
        expected: &<Circuit as Environment>::BaseField,
        a: &Field<Circuit>,
        b: &Field<Circuit>,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scope(name, || {
            let candidate = a.pow(b);
            assert_eq!(*expected, candidate.eject_value(), "({}^{})", a.eject_value(), b.eject_value());
            assert_scope!(num_constants, num_public, num_private, num_constraints);
        });
    }

    #[test]
    fn test_constant_pow_constant() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::BaseField = UniformRand::rand(&mut test_rng());
            let second: <Circuit as Environment>::BaseField = UniformRand::rand(&mut test_rng());

            let expected = first.pow(second.to_repr().0);
            let a = Field::<Circuit>::new(Mode::Constant, first);
            let b = Field::<Circuit>::new(Mode::Constant, second);

            let name = format!("Pow: a^b {}", i);
            check_pow(&name, &expected, &a, &b, 253, 0, 0, 0);
        }
    }

    #[test]
    fn test_constant_pow_public() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::BaseField = UniformRand::rand(&mut test_rng());
            let second: <Circuit as Environment>::BaseField = UniformRand::rand(&mut test_rng());

            let expected = first.pow(second.to_repr().0);
            let a = Field::<Circuit>::new(Mode::Constant, first);
            let b = Field::<Circuit>::new(Mode::Public, second);

            let name = format!("Pow: a^b {}", i);
            check_pow(&name, &expected, &a, &b, 0, 0, 757, 758);
        }
    }

    #[test]
    fn test_constant_pow_private() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::BaseField = UniformRand::rand(&mut test_rng());
            let second: <Circuit as Environment>::BaseField = UniformRand::rand(&mut test_rng());

            let expected = first.pow(second.to_repr().0);
            let a = Field::<Circuit>::new(Mode::Constant, first);
            let b = Field::<Circuit>::new(Mode::Private, second);

            let name = format!("Pow: a^b {}", i);
            check_pow(&name, &expected, &a, &b, 0, 0, 757, 758);
        }
    }

    #[test]
    fn test_public_pow_constant() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::BaseField = UniformRand::rand(&mut test_rng());
            let second: <Circuit as Environment>::BaseField = UniformRand::rand(&mut test_rng());

            let expected = first.pow(second.to_repr().0);
            let a = Field::<Circuit>::new(Mode::Public, first);
            let b = Field::<Circuit>::new(Mode::Constant, second);

            // Find the first instance (from the MSB) of a `true` bit.
            let exponent_bits = second.to_bits_be();
            let index = exponent_bits
                .iter()
                .position(|b| *b)
                .unwrap_or(<Circuit as Environment>::BaseField::size_in_bits() - 1);

            // Calculate the number of squares and multiplications as follows:
            //   `num_squares` := number of remaining bits after the first nonzero bit (from MSB -> LSB)
            //   `num_multiplications` := number of `true` bits after the first nonzero bit (from MSB -> LSB)
            let num_squares = <Circuit as Environment>::BaseField::size_in_bits() - index - 1;
            let num_multiplications = exponent_bits[index + 1..].iter().map(|bit| *bit as usize).sum::<usize>();

            // The number of private variables and constraints are both: num_squares + num_multiplications
            let name = format!("Pow: a^b {}", i);
            let num_private = num_squares + num_multiplications;
            let num_constraints = num_private;
            check_pow(&name, &expected, &a, &b, 253, 0, num_private, num_constraints);
        }
    }

    #[test]
    fn test_private_pow_constant() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::BaseField = UniformRand::rand(&mut test_rng());
            let second: <Circuit as Environment>::BaseField = UniformRand::rand(&mut test_rng());

            let expected = first.pow(second.to_repr().0);
            let a = Field::<Circuit>::new(Mode::Private, first);
            let b = Field::<Circuit>::new(Mode::Constant, second);

            // Find the first instance (from the MSB) of a `true` bit.
            let exponent_bits = second.to_bits_be();
            let index = exponent_bits
                .iter()
                .position(|b| *b)
                .unwrap_or(<Circuit as Environment>::BaseField::size_in_bits() - 1);

            // Calculate the number of squares and multiplications as follows:
            //   `num_squares` := number of remaining bits after the first nonzero bit (from MSB -> LSB)
            //   `num_multiplications` := number of `true` bits after the first nonzero bit (from MSB -> LSB)
            let num_squares = <Circuit as Environment>::BaseField::size_in_bits() - index - 1;
            let num_multiplications = exponent_bits[index + 1..].iter().map(|bit| *bit as usize).sum::<usize>();

            // The number of private variables and constraints are both: num_squares + num_multiplications
            let name = format!("Pow: a^b {}", i);
            let num_private = num_squares + num_multiplications;
            let num_constraints = num_private;
            check_pow(&name, &expected, &a, &b, 253, 0, num_private, num_constraints);
        }
    }

    #[test]
    fn test_public_pow_public() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::BaseField = UniformRand::rand(&mut test_rng());
            let second: <Circuit as Environment>::BaseField = UniformRand::rand(&mut test_rng());

            let expected = first.pow(second.to_repr().0);
            let a = Field::<Circuit>::new(Mode::Public, first);
            let b = Field::<Circuit>::new(Mode::Public, second);

            let name = format!("Pow: a^b {}", i);
            check_pow(&name, &expected, &a, &b, 0, 0, 1010, 1011);
        }
    }

    #[test]
    fn test_public_pow_private() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::BaseField = UniformRand::rand(&mut test_rng());
            let second: <Circuit as Environment>::BaseField = UniformRand::rand(&mut test_rng());

            let expected = first.pow(second.to_repr().0);
            let a = Field::<Circuit>::new(Mode::Public, first);
            let b = Field::<Circuit>::new(Mode::Private, second);

            let name = format!("Pow: a^b {}", i);
            check_pow(&name, &expected, &a, &b, 0, 0, 1010, 1011);
        }
    }

    #[test]
    fn test_private_pow_public() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::BaseField = UniformRand::rand(&mut test_rng());
            let second: <Circuit as Environment>::BaseField = UniformRand::rand(&mut test_rng());

            let expected = first.pow(second.to_repr().0);
            let a = Field::<Circuit>::new(Mode::Private, first);
            let b = Field::<Circuit>::new(Mode::Public, second);

            let name = format!("Pow: a^b {}", i);
            check_pow(&name, &expected, &a, &b, 0, 0, 1010, 1011);
        }
    }

    #[test]
    fn test_private_pow_private() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::BaseField = UniformRand::rand(&mut test_rng());
            let second: <Circuit as Environment>::BaseField = UniformRand::rand(&mut test_rng());

            let expected = first.pow(second.to_repr().0);
            let a = Field::<Circuit>::new(Mode::Private, first);
            let b = Field::<Circuit>::new(Mode::Private, second);

            let name = format!("Pow: a^b {}", i);
            check_pow(&name, &expected, &a, &b, 0, 0, 1010, 1011);
        }
    }
}
