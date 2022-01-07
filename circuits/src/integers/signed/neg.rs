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
use crate::{BaseField, One, RippleCarryAdder, Zero};
use num_traits::CheckedNeg;
use snarkvm_fields::PrimeField;

impl<E: Environment, I, const SIZE: usize> Neg for Signed<E, I, SIZE>
where
    I: 'static + PrimInt + NumSigned + Bounded + NumZero + NumOne + CheckedNeg,
    bool: AsPrimitive<I>,
{
    type Output = Self;

    fn neg(self) -> Self::Output {
        let value = match self.eject_value().checked_neg() {
            Some(value) => value,
            None => E::halt("Signed integer overflow during negation."),
        };

        //TODO (@pranav) Understand why the `gadgets/` implementation doesn't explicitly check that the result is well formed
        // flip all bits
        let flipped: Vec<Boolean<E>> = self.bits_le.iter().map(|bit| !bit).collect();

        // add one
        let mut one = vec![Boolean::new(Mode::Constant, true)];
        one.append(&mut vec![Boolean::new(Mode::Constant, false); SIZE - 1]);

        let mut bits = flipped.add_bits(&one);
        let _carry = bits.pop(); // we already accounted for overflow above

        Signed::from_bits(bits)
    }
}

impl<E: Environment, I, const SIZE: usize> Neg for &Signed<E, I, SIZE>
where
    I: 'static + PrimInt + NumSigned + Bounded + NumZero + NumOne + CheckedNeg,
    bool: AsPrimitive<I>,
{
    type Output = Signed<E, I, SIZE>;

    fn neg(self) -> Self::Output {
        -(self.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

    const ITERATIONS: usize = 100;

    fn check_neg(
        name: &str,
        expected: i64,
        candidate_input: Signed<Circuit, i64, 64>,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, |scope| {
            let candidate_output = -candidate_input;
            assert_eq!(expected, candidate_output.eject_value());

            // assert_eq!(num_constants, scope.num_constants_in_scope());
            // assert_eq!(num_public, scope.num_public_in_scope());
            // assert_eq!(num_private, scope.num_private_in_scope());
            // assert_eq!(num_constraints, scope.num_constraints_in_scope());
            assert!(Circuit::is_satisfied());
        });
    }

    #[test]
    fn test_neg_constant() {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let value: i64 = UniformRand::rand(&mut thread_rng());
            let expected = match value.checked_neg() {
                Some(expected) => expected,
                None => continue,
            };

            let candidate_input = Signed::<Circuit, i64, 64>::new(Mode::Constant, value);
            check_neg(&format!("NEG Constant {}", i), expected, candidate_input, 0, 0, 0, 0);
        }
    }

    #[test]
    fn test_neg_public() {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let value: i64 = UniformRand::rand(&mut thread_rng());
            let expected = match value.checked_neg() {
                Some(expected) => expected,
                None => continue,
            };

            let candidate_input = Signed::<Circuit, i64, 64>::new(Mode::Public, value);
            check_neg(&format!("NEG Public {}", i), expected, candidate_input, 0, 0, 0, 0);
        }
    }

    #[test]
    fn test_neg_private() {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let value: i64 = UniformRand::rand(&mut thread_rng());
            let expected = match value.checked_neg() {
                Some(expected) => expected,
                None => continue,
            };

            let candidate_input = Signed::<Circuit, i64, 64>::new(Mode::Private, value);
            check_neg(&format!("NEG Private {}", i), expected, candidate_input, 0, 0, 0, 0);
        }
    }
}
