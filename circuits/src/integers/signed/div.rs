// Copyright (C) 2019-2021 Aleo Systems Inc.
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

impl<E: Environment, I: PrimitiveSignedInteger, const SIZE: usize> Div<Self> for Signed<E, I, SIZE> {
    type Output = Self;

    fn div(self, other: Self) -> Self::Output {
        self / &other
    }
}

impl<E: Environment, I: PrimitiveSignedInteger, const SIZE: usize> Div<&Self> for Signed<E, I, SIZE> {
    type Output = Self;

    fn div(self, other: &Self) -> Self::Output {
        // Determine the variable mode.
        let mode = match self.is_constant() && other.is_constant() {
            true => Mode::Constant,
            false => Mode::Private,
        };

        // Directly compute the quotient, check for overflow or division by zero.
        let other_value = other.eject_value();
        let value = match self.eject_value().checked_div(&other_value) {
            Some(value) => value,
            None => {
                if other_value == I::zero() {
                    E::halt("Division by zero.")
                } else {
                    E::halt("Signed integer overflow during division.")
                }
            }
        };

        if mode.is_constant() {
            return Signed::new(mode, value);
        }

        // N / D pseudocode:
        //
        // if D = 0 then error(DivisionByZeroException) end
        //
        // positive = msb(N) == msb(D) -- if msb's equal, return positive result
        //
        // Q := 0                  -- Initialize quotient and remainder to zero
        // R := 0
        //
        // for i := n − 1 .. 0 do  -- Where n is number of bits in N
        //   R := R << 1           -- Left-shift R by 1 bit
        //   R(0) := N(i)          -- Set the least-significant bit of R equal to bit i of the numerator
        //   if R ≥ D then
        //     R := R − D
        //     Q(i) := 1
        //   end
        // end
        //
        // if positive then           -- positive result
        //    Q
        // else
        //    !Q                      -- negative result

        // Division by zero is already checked above.
        let a_msb = self.bits_le.last().unwrap();
        let b_msb = other.bits_le.last().unwrap();
        let positive = a_msb.is_eq(&b_msb);

        let a_absolute_value = Self::from_bits(
            self.bits_le
                .iter()
                .map(|bit| Boolean::ternary(a_msb, &!bit, bit))
                .collect(),
        );
        let b_absolute_value = Self::from_bits(
            other
                .bits_le
                .iter()
                .map(|bit| Boolean::ternary(b_msb, &!bit, bit))
                .collect(),
        );

        let mut quotient_bits = Vec::with_capacity(SIZE);
        let mut remainder: Signed<E, I, SIZE> = Self::from_bits(vec![Boolean::new(mode, false); SIZE]);

        // TODO (@pranav) Fix use of clones for `remainder`
        // for i := n - 1 .. 0 do
        for (i, bit) in a_absolute_value.bits_le.iter().rev().enumerate() {
            // R := R << 1
            remainder = remainder.clone() + &remainder;

            // R(0) := N(i)
            let remainder_plus_one = remainder.clone().add(&Signed::new(Mode::Constant, I::one()));
            remainder = Signed::ternary(bit, &remainder_plus_one, &remainder.clone());

            // if R ≥ D
            let r_larger_or_equal_to_d = !remainder.is_lt(&b_absolute_value);

            // compute R - D
            let r_sub_d = remainder.clone().sub(&b_absolute_value);

            remainder = Signed::ternary(&r_larger_or_equal_to_d, &r_sub_d, &remainder.clone());

            // Q(i) := 1
            quotient_bits.push(r_larger_or_equal_to_d);
        }

        let result_bits: Vec<Boolean<E>> = quotient_bits
            .iter()
            .rev()
            .map(|bit| Boolean::ternary(&positive, bit, &!bit))
            .collect();

        Signed::from_bits(result_bits)
    }
}

impl<E: Environment, I: PrimitiveSignedInteger, const SIZE: usize> Div<Signed<E, I, SIZE>> for &Signed<E, I, SIZE> {
    type Output = Signed<E, I, SIZE>;

    fn div(self, other: Signed<E, I, SIZE>) -> Self::Output {
        (*self).clone() / other
    }
}

impl<E: Environment, I: PrimitiveSignedInteger, const SIZE: usize> Div<&Signed<E, I, SIZE>> for &Signed<E, I, SIZE> {
    type Output = Signed<E, I, SIZE>;

    fn div(self, other: &Signed<E, I, SIZE>) -> Self::Output {
        (*self).clone() / other
    }
}

impl<E: Environment, I: PrimitiveSignedInteger, const SIZE: usize> DivAssign<Self> for Signed<E, I, SIZE> {
    fn div_assign(&mut self, other: Self) {
        *self /= &other;
    }
}

impl<E: Environment, I: PrimitiveSignedInteger, const SIZE: usize> DivAssign<&Self> for Signed<E, I, SIZE> {
    fn div_assign(&mut self, other: &Self) {
        *self = self.clone() / other;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use num_traits::CheckedDiv;
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

    const ITERATIONS: usize = 100;

    fn check_div(
        name: &str,
        expected: i64,
        a: &Signed<Circuit, i64, 64>,
        b: &Signed<Circuit, i64, 64>,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, |scope| {
            let candidate = a / b;
            assert_eq!(
                expected,
                candidate.eject_value(),
                "{} != {} := ({} / {})",
                expected,
                candidate.eject_value(),
                a.eject_value(),
                b.eject_value()
            );

            // assert_eq!(num_constants, scope.num_constants_in_scope());
            // assert_eq!(num_public, scope.num_public_in_scope());
            // assert_eq!(num_private, scope.num_private_in_scope());
            // assert_eq!(num_constraints, scope.num_constraints_in_scope());
            assert!(Circuit::is_satisfied());
        });
    }

    fn check_div_assign(
        name: &str,
        expected: i64,
        a: &Signed<Circuit, i64, 64>,
        b: &Signed<Circuit, i64, 64>,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, |scope| {
            let mut candidate = a.clone();
            candidate /= b;
            assert_eq!(
                expected,
                candidate.eject_value(),
                "{} != {} := ({} / {})",
                expected,
                candidate.eject_value(),
                a.eject_value(),
                b.eject_value()
            );

            // assert_eq!(num_constants, scope.num_constants_in_scope());
            // assert_eq!(num_public, scope.num_public_in_scope());
            // assert_eq!(num_private, scope.num_private_in_scope());
            // assert_eq!(num_constraints, scope.num_constraints_in_scope());
            assert!(Circuit::is_satisfied());
        });
    }

    #[test]
    fn test_constant_div_constant() {
        for i in 0..ITERATIONS {
            let dividend: i64 = UniformRand::rand(&mut thread_rng());
            let divisor: i64 = UniformRand::rand(&mut thread_rng());

            let expected = match dividend.checked_div(divisor) {
                Some(expected) => expected,
                None => continue,
            };
            let a = Signed::new(Mode::Constant, dividend);
            let b = Signed::new(Mode::Constant, divisor);

            let name = format!("Div: a / b {}", i);
            check_div(&name, expected, &a, &b, 1757, 0, 0, 0);
            let name = format!("DivAssign: a / b {}", i);
            check_div_assign(&name, expected, &a, &b, 1757, 0, 0, 0);
        }
    }

    #[test]
    fn test_constant_div_public() {
        for i in 0..ITERATIONS {
            let dividend: i64 = UniformRand::rand(&mut thread_rng());
            let divisor: i64 = UniformRand::rand(&mut thread_rng());

            let expected = match dividend.checked_div(divisor) {
                Some(expected) => expected,
                None => continue,
            };
            let a = Signed::new(Mode::Constant, dividend);
            let b = Signed::new(Mode::Public, divisor);

            let name = format!("Div: a / b {}", i);
            check_div(&name, expected, &a, &b, 757, 0, 2500, 2500);
            let name = format!("DivAssign: a / b {}", i);
            check_div_assign(&name, expected, &a, &b, 757, 0, 2500, 2500);
        }
    }

    #[test]
    fn test_constant_div_private() {
        for i in 0..ITERATIONS {
            let dividend: i64 = UniformRand::rand(&mut thread_rng());
            let divisor: i64 = UniformRand::rand(&mut thread_rng());

            let expected = match dividend.checked_div(divisor) {
                Some(expected) => expected,
                None => continue,
            };
            let a = Signed::new(Mode::Constant, dividend);
            let b = Signed::new(Mode::Private, divisor);

            let name = format!("Div: a / b {}", i);
            check_div(&name, expected, &a, &b, 757, 0, 2500, 2500);
            let name = format!("DivAssign: a / b {}", i);
            check_div_assign(&name, expected, &a, &b, 757, 0, 2500, 2500);
        }
    }

    #[test]
    fn test_public_div_public() {
        for i in 0..ITERATIONS {
            let dividend: i64 = UniformRand::rand(&mut thread_rng());
            let divisor: i64 = UniformRand::rand(&mut thread_rng());

            let expected = match dividend.checked_div(divisor) {
                Some(expected) => expected,
                None => continue,
            };
            let a = Signed::new(Mode::Public, dividend);
            let b = Signed::new(Mode::Public, divisor);

            let name = format!("Div: a / b {}", i);
            check_div(&name, expected, &a, &b, 755, 0, 3255, 3255);
            let name = format!("DivAssign: a / b {}", i);
            check_div_assign(&name, expected, &a, &b, 755, 0, 3255, 3255);
        }
    }

    #[test]
    fn test_public_div_private() {
        for i in 0..ITERATIONS {
            let dividend: i64 = UniformRand::rand(&mut thread_rng());
            let divisor: i64 = UniformRand::rand(&mut thread_rng());

            let expected = match dividend.checked_div(divisor) {
                Some(expected) => expected,
                None => continue,
            };
            let a = Signed::new(Mode::Public, dividend);
            let b = Signed::new(Mode::Private, divisor);

            let name = format!("Div: a / b {}", i);
            check_div(&name, expected, &a, &b, 755, 0, 3255, 3255);
            let name = format!("DivAssign: a / b {}", i);
            check_div_assign(&name, expected, &a, &b, 755, 0, 3255, 3255);
        }
    }

    #[test]
    fn test_private_div_public() {
        for i in 0..ITERATIONS {
            let dividend: i64 = UniformRand::rand(&mut thread_rng());
            let divisor: i64 = UniformRand::rand(&mut thread_rng());

            let expected = match dividend.checked_div(divisor) {
                Some(expected) => expected,
                None => continue,
            };
            let a = Signed::new(Mode::Private, dividend);
            let b = Signed::new(Mode::Public, divisor);

            let name = format!("Div: a / b {}", i);
            check_div(&name, expected, &a, &b, 755, 0, 3255, 3255);
            let name = format!("DivAssign: a / b {}", i);
            check_div_assign(&name, expected, &a, &b, 755, 0, 3255, 3255);
        }
    }

    #[test]
    fn test_private_div_private() {
        for i in 0..ITERATIONS {
            let dividend: i64 = UniformRand::rand(&mut thread_rng());
            let divisor: i64 = UniformRand::rand(&mut thread_rng());

            let expected = match dividend.checked_div(divisor) {
                Some(expected) => expected,
                None => continue,
            };
            let a = Signed::new(Mode::Private, dividend);
            let b = Signed::new(Mode::Private, divisor);

            let name = format!("Div: a / b {}", i);
            check_div(&name, expected, &a, &b, 755, 0, 3255, 3255);
            let name = format!("DivAssign: a / b {}", i);
            check_div_assign(&name, expected, &a, &b, 755, 0, 3255, 3255);
        }
    }

    #[test]
    fn test_div_matches() {
        for i in 0..ITERATIONS {
            let dividend: i64 = UniformRand::rand(&mut thread_rng());
            let divisor: i64 = UniformRand::rand(&mut thread_rng());

            let expected = match dividend.checked_div(divisor) {
                Some(expected) => expected,
                None => continue,
            };

            // Constant
            let a = Signed::<Circuit, i64, 64>::new(Mode::Constant, dividend);
            let b = Signed::<Circuit, i64, 64>::new(Mode::Constant, divisor);
            let candidate = a / b;
            assert_eq!(expected, candidate.eject_value());

            // Private
            let a = Signed::<Circuit, i64, 64>::new(Mode::Private, dividend);
            let b = Signed::<Circuit, i64, 64>::new(Mode::Private, divisor);
            let candidate = a / b;
            assert_eq!(expected, candidate.eject_value());
        }
    }
}
