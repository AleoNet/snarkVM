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
use itertools::Itertools;

impl<E: Environment, I: IntegerType> Ternary for Integer<E, I> {
    type Boolean = Boolean<E>;
    type Output = Self;

    /// Returns `first` if `condition` is `true`, otherwise returns `second`.
    fn ternary(condition: &Self::Boolean, first: &Self, second: &Self) -> Self::Output {
        // Constant `condition`
        if condition.is_constant() {
            match condition.eject_value() {
                true => first.clone(),
                false => second.clone(),
            }
        }
        // Variables
        else {
            // Directly instantiate the integer, rather than invoking `from_bits_le`
            // since the modes of each individual bit varies depending on the modes
            // and values of `condition`, `first_bit`, and `second_bit`.
            Self {
                bits_le: first
                    .bits_le
                    .iter()
                    .zip_eq(second.bits_le.iter())
                    .map(|(first_bit, second_bit)| Self::Boolean::ternary(&condition, first_bit, second_bit))
                    .collect(),
                phantom: Default::default(),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;
    use test_utilities::*;

    use rand::thread_rng;

    #[rustfmt::skip]
    fn run_test<I: IntegerType>(
        mode_condition: Mode,
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        for flag in vec![true, false] {
            let first: I = UniformRand::rand(&mut thread_rng());
            let second: I = UniformRand::rand(&mut thread_rng());

            let name = format!("Ternary({}): if ({}) then ({}) else ({})", flag, mode_condition, mode_a, mode_b);
            let case = format!("if ({}) then ({}) else ({})", flag, first, second);

            let condition = Boolean::<Circuit>::new(mode_condition, flag);
            let a = Integer::<Circuit, I>::new(mode_a, first);
            let b = Integer::new(mode_b, second);

            // Capture the condition in a closure and use the binary operation check.
            let operation = | a: &Integer<Circuit, I>, b: &Integer<Circuit, I> | { Integer::ternary(&condition, a, b) };
            check_binary_operation_passes(&name, &case, if flag { first } else { second }, &a, &b, operation, num_constants, num_public, num_private, num_constraints);
        }
    }

    // Tests for u8.

    #[test]
    fn test_u8_if_constant_then_constant_else_constant() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_if_constant_then_constant_else_public() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Constant, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_if_constant_then_constant_else_private() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Constant, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_if_constant_then_public_else_constant() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_if_constant_then_public_else_public() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Public, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_if_constant_then_public_else_private() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Public, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_if_constant_then_private_else_constant() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_if_constant_then_private_else_public() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Private, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_if_constant_then_private_else_private() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Private, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_if_public_then_constant_else_constant() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_if_public_then_constant_else_public() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Constant, Mode::Public, 0, 0, 8, 8);
    }

    #[test]
    fn test_u8_if_public_then_constant_else_private() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Constant, Mode::Private, 0, 0, 8, 8);
    }

    #[test]
    fn test_u8_if_public_then_public_else_constant() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Public, Mode::Constant, 0, 0, 8, 8);
    }

    #[test]
    fn test_u8_if_public_then_public_else_public() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Public, Mode::Public, 0, 0, 8, 8);
    }

    #[test]
    fn test_u8_if_public_then_public_else_private() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Public, Mode::Private, 0, 0, 8, 8);
    }

    #[test]
    fn test_u8_if_public_then_private_else_constant() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Private, Mode::Constant, 0, 0, 8, 8);
    }

    #[test]
    fn test_u8_if_public_then_private_else_public() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Private, Mode::Public, 0, 0, 8, 8);
    }

    #[test]
    fn test_u8_if_public_then_private_else_private() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Private, Mode::Private, 0, 0, 8, 8);
    }

    #[test]
    fn test_u8_if_private_then_constant_else_constant() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_if_private_then_constant_else_public() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Constant, Mode::Public, 0, 0, 8, 8);
    }

    #[test]
    fn test_u8_if_private_then_constant_else_private() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Constant, Mode::Private, 0, 0, 8, 8);
    }

    #[test]
    fn test_u8_if_private_then_public_else_constant() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Public, Mode::Constant, 0, 0, 8, 8);
    }

    #[test]
    fn test_u8_if_private_then_public_else_public() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Public, Mode::Public, 0, 0, 8, 8);
    }

    #[test]
    fn test_u8_if_private_then_public_else_private() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Public, Mode::Private, 0, 0, 8, 8);
    }

    #[test]
    fn test_u8_if_private_then_private_else_constant() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Private, Mode::Constant, 0, 0, 8, 8);
    }

    #[test]
    fn test_u8_if_private_then_private_else_public() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Private, Mode::Public, 0, 0, 8, 8);
    }

    #[test]
    fn test_u8_if_private_then_private_else_private() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Private, Mode::Private, 0, 0, 8, 8);
    }

    // Tests for i8.

    #[test]
    fn test_i8_if_constant_then_constant_else_constant() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_if_constant_then_constant_else_public() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Constant, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_if_constant_then_constant_else_private() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Constant, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_if_constant_then_public_else_constant() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_if_constant_then_public_else_public() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Public, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_if_constant_then_public_else_private() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Public, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_if_constant_then_private_else_constant() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_if_constant_then_private_else_public() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Private, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_if_constant_then_private_else_private() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Private, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_if_public_then_constant_else_constant() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_if_public_then_constant_else_public() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Constant, Mode::Public, 0, 0, 8, 8);
    }

    #[test]
    fn test_i8_if_public_then_constant_else_private() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Constant, Mode::Private, 0, 0, 8, 8);
    }

    #[test]
    fn test_i8_if_public_then_public_else_constant() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Public, Mode::Constant, 0, 0, 8, 8);
    }

    #[test]
    fn test_i8_if_public_then_public_else_public() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Public, Mode::Public, 0, 0, 8, 8);
    }

    #[test]
    fn test_i8_if_public_then_public_else_private() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Public, Mode::Private, 0, 0, 8, 8);
    }

    #[test]
    fn test_i8_if_public_then_private_else_constant() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Private, Mode::Constant, 0, 0, 8, 8);
    }

    #[test]
    fn test_i8_if_public_then_private_else_public() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Private, Mode::Public, 0, 0, 8, 8);
    }

    #[test]
    fn test_i8_if_public_then_private_else_private() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Private, Mode::Private, 0, 0, 8, 8);
    }

    #[test]
    fn test_i8_if_private_then_constant_else_constant() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_if_private_then_constant_else_public() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Constant, Mode::Public, 0, 0, 8, 8);
    }

    #[test]
    fn test_i8_if_private_then_constant_else_private() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Constant, Mode::Private, 0, 0, 8, 8);
    }

    #[test]
    fn test_i8_if_private_then_public_else_constant() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Public, Mode::Constant, 0, 0, 8, 8);
    }

    #[test]
    fn test_i8_if_private_then_public_else_public() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Public, Mode::Public, 0, 0, 8, 8);
    }

    #[test]
    fn test_i8_if_private_then_public_else_private() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Public, Mode::Private, 0, 0, 8, 8);
    }

    #[test]
    fn test_i8_if_private_then_private_else_constant() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Private, Mode::Constant, 0, 0, 8, 8);
    }

    #[test]
    fn test_i8_if_private_then_private_else_public() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Private, Mode::Public, 0, 0, 8, 8);
    }

    #[test]
    fn test_i8_if_private_then_private_else_private() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Private, Mode::Private, 0, 0, 8, 8);
    }

    // Tests for u16.

    #[test]
    fn test_u16_if_constant_then_constant_else_constant() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_if_constant_then_constant_else_public() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Constant, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_if_constant_then_constant_else_private() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Constant, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_if_constant_then_public_else_constant() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_if_constant_then_public_else_public() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Public, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_if_constant_then_public_else_private() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Public, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_if_constant_then_private_else_constant() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_if_constant_then_private_else_public() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Private, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_if_constant_then_private_else_private() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Private, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_if_public_then_constant_else_constant() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_if_public_then_constant_else_public() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Constant, Mode::Public, 0, 0, 16, 16);
    }

    #[test]
    fn test_u16_if_public_then_constant_else_private() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Constant, Mode::Private, 0, 0, 16, 16);
    }

    #[test]
    fn test_u16_if_public_then_public_else_constant() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Public, Mode::Constant, 0, 0, 16, 16);
    }

    #[test]
    fn test_u16_if_public_then_public_else_public() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Public, Mode::Public, 0, 0, 16, 16);
    }

    #[test]
    fn test_u16_if_public_then_public_else_private() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Public, Mode::Private, 0, 0, 16, 16);
    }

    #[test]
    fn test_u16_if_public_then_private_else_constant() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Private, Mode::Constant, 0, 0, 16, 16);
    }

    #[test]
    fn test_u16_if_public_then_private_else_public() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Private, Mode::Public, 0, 0, 16, 16);
    }

    #[test]
    fn test_u16_if_public_then_private_else_private() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Private, Mode::Private, 0, 0, 16, 16);
    }

    #[test]
    fn test_u16_if_private_then_constant_else_constant() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_if_private_then_constant_else_public() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Constant, Mode::Public, 0, 0, 16, 16);
    }

    #[test]
    fn test_u16_if_private_then_constant_else_private() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Constant, Mode::Private, 0, 0, 16, 16);
    }

    #[test]
    fn test_u16_if_private_then_public_else_constant() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Public, Mode::Constant, 0, 0, 16, 16);
    }

    #[test]
    fn test_u16_if_private_then_public_else_public() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Public, Mode::Public, 0, 0, 16, 16);
    }

    #[test]
    fn test_u16_if_private_then_public_else_private() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Public, Mode::Private, 0, 0, 16, 16);
    }

    #[test]
    fn test_u16_if_private_then_private_else_constant() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Private, Mode::Constant, 0, 0, 16, 16);
    }

    #[test]
    fn test_u16_if_private_then_private_else_public() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Private, Mode::Public, 0, 0, 16, 16);
    }

    #[test]
    fn test_u16_if_private_then_private_else_private() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Private, Mode::Private, 0, 0, 16, 16);
    }

    // Tests for i16.

    #[test]
    fn test_i16_if_constant_then_constant_else_constant() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_if_constant_then_constant_else_public() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Constant, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_if_constant_then_constant_else_private() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Constant, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_if_constant_then_public_else_constant() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_if_constant_then_public_else_public() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Public, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_if_constant_then_public_else_private() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Public, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_if_constant_then_private_else_constant() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_if_constant_then_private_else_public() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Private, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_if_constant_then_private_else_private() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Private, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_if_public_then_constant_else_constant() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_if_public_then_constant_else_public() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Constant, Mode::Public, 0, 0, 16, 16);
    }

    #[test]
    fn test_i16_if_public_then_constant_else_private() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Constant, Mode::Private, 0, 0, 16, 16);
    }

    #[test]
    fn test_i16_if_public_then_public_else_constant() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Public, Mode::Constant, 0, 0, 16, 16);
    }

    #[test]
    fn test_i16_if_public_then_public_else_public() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Public, Mode::Public, 0, 0, 16, 16);
    }

    #[test]
    fn test_i16_if_public_then_public_else_private() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Public, Mode::Private, 0, 0, 16, 16);
    }

    #[test]
    fn test_i16_if_public_then_private_else_constant() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Private, Mode::Constant, 0, 0, 16, 16);
    }

    #[test]
    fn test_i16_if_public_then_private_else_public() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Private, Mode::Public, 0, 0, 16, 16);
    }

    #[test]
    fn test_i16_if_public_then_private_else_private() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Private, Mode::Private, 0, 0, 16, 16);
    }

    #[test]
    fn test_i16_if_private_then_constant_else_constant() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_if_private_then_constant_else_public() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Constant, Mode::Public, 0, 0, 16, 16);
    }

    #[test]
    fn test_i16_if_private_then_constant_else_private() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Constant, Mode::Private, 0, 0, 16, 16);
    }

    #[test]
    fn test_i16_if_private_then_public_else_constant() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Public, Mode::Constant, 0, 0, 16, 16);
    }

    #[test]
    fn test_i16_if_private_then_public_else_public() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Public, Mode::Public, 0, 0, 16, 16);
    }

    #[test]
    fn test_i16_if_private_then_public_else_private() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Public, Mode::Private, 0, 0, 16, 16);
    }

    #[test]
    fn test_i16_if_private_then_private_else_constant() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Private, Mode::Constant, 0, 0, 16, 16);
    }

    #[test]
    fn test_i16_if_private_then_private_else_public() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Private, Mode::Public, 0, 0, 16, 16);
    }

    #[test]
    fn test_i16_if_private_then_private_else_private() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Private, Mode::Private, 0, 0, 16, 16);
    }

    // Tests for u32.

    #[test]
    fn test_u32_if_constant_then_constant_else_constant() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_if_constant_then_constant_else_public() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Constant, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_if_constant_then_constant_else_private() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Constant, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_if_constant_then_public_else_constant() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_if_constant_then_public_else_public() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Public, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_if_constant_then_public_else_private() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Public, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_if_constant_then_private_else_constant() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_if_constant_then_private_else_public() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Private, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_if_constant_then_private_else_private() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Private, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_if_public_then_constant_else_constant() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_if_public_then_constant_else_public() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Constant, Mode::Public, 0, 0, 32, 32);
    }

    #[test]
    fn test_u32_if_public_then_constant_else_private() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Constant, Mode::Private, 0, 0, 32, 32);
    }

    #[test]
    fn test_u32_if_public_then_public_else_constant() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Public, Mode::Constant, 0, 0, 32, 32);
    }

    #[test]
    fn test_u32_if_public_then_public_else_public() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Public, Mode::Public, 0, 0, 32, 32);
    }

    #[test]
    fn test_u32_if_public_then_public_else_private() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Public, Mode::Private, 0, 0, 32, 32);
    }

    #[test]
    fn test_u32_if_public_then_private_else_constant() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Private, Mode::Constant, 0, 0, 32, 32);
    }

    #[test]
    fn test_u32_if_public_then_private_else_public() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Private, Mode::Public, 0, 0, 32, 32);
    }

    #[test]
    fn test_u32_if_public_then_private_else_private() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Private, Mode::Private, 0, 0, 32, 32);
    }

    #[test]
    fn test_u32_if_private_then_constant_else_constant() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_if_private_then_constant_else_public() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Constant, Mode::Public, 0, 0, 32, 32);
    }

    #[test]
    fn test_u32_if_private_then_constant_else_private() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Constant, Mode::Private, 0, 0, 32, 32);
    }

    #[test]
    fn test_u32_if_private_then_public_else_constant() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Public, Mode::Constant, 0, 0, 32, 32);
    }

    #[test]
    fn test_u32_if_private_then_public_else_public() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Public, Mode::Public, 0, 0, 32, 32);
    }

    #[test]
    fn test_u32_if_private_then_public_else_private() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Public, Mode::Private, 0, 0, 32, 32);
    }

    #[test]
    fn test_u32_if_private_then_private_else_constant() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Private, Mode::Constant, 0, 0, 32, 32);
    }

    #[test]
    fn test_u32_if_private_then_private_else_public() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Private, Mode::Public, 0, 0, 32, 32);
    }

    #[test]
    fn test_u32_if_private_then_private_else_private() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Private, Mode::Private, 0, 0, 32, 32);
    }

    // Tests for i32.

    #[test]
    fn test_i32_if_constant_then_constant_else_constant() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_if_constant_then_constant_else_public() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Constant, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_if_constant_then_constant_else_private() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Constant, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_if_constant_then_public_else_constant() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_if_constant_then_public_else_public() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Public, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_if_constant_then_public_else_private() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Public, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_if_constant_then_private_else_constant() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_if_constant_then_private_else_public() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Private, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_if_constant_then_private_else_private() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Private, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_if_public_then_constant_else_constant() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_if_public_then_constant_else_public() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Constant, Mode::Public, 0, 0, 32, 32);
    }

    #[test]
    fn test_i32_if_public_then_constant_else_private() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Constant, Mode::Private, 0, 0, 32, 32);
    }

    #[test]
    fn test_i32_if_public_then_public_else_constant() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Public, Mode::Constant, 0, 0, 32, 32);
    }

    #[test]
    fn test_i32_if_public_then_public_else_public() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Public, Mode::Public, 0, 0, 32, 32);
    }

    #[test]
    fn test_i32_if_public_then_public_else_private() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Public, Mode::Private, 0, 0, 32, 32);
    }

    #[test]
    fn test_i32_if_public_then_private_else_constant() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Private, Mode::Constant, 0, 0, 32, 32);
    }

    #[test]
    fn test_i32_if_public_then_private_else_public() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Private, Mode::Public, 0, 0, 32, 32);
    }

    #[test]
    fn test_i32_if_public_then_private_else_private() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Private, Mode::Private, 0, 0, 32, 32);
    }

    #[test]
    fn test_i32_if_private_then_constant_else_constant() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_if_private_then_constant_else_public() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Constant, Mode::Public, 0, 0, 32, 32);
    }

    #[test]
    fn test_i32_if_private_then_constant_else_private() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Constant, Mode::Private, 0, 0, 32, 32);
    }

    #[test]
    fn test_i32_if_private_then_public_else_constant() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Public, Mode::Constant, 0, 0, 32, 32);
    }

    #[test]
    fn test_i32_if_private_then_public_else_public() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Public, Mode::Public, 0, 0, 32, 32);
    }

    #[test]
    fn test_i32_if_private_then_public_else_private() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Public, Mode::Private, 0, 0, 32, 32);
    }

    #[test]
    fn test_i32_if_private_then_private_else_constant() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Private, Mode::Constant, 0, 0, 32, 32);
    }

    #[test]
    fn test_i32_if_private_then_private_else_public() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Private, Mode::Public, 0, 0, 32, 32);
    }

    #[test]
    fn test_i32_if_private_then_private_else_private() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Private, Mode::Private, 0, 0, 32, 32);
    }

    // Tests for u64.

    #[test]
    fn test_u64_if_constant_then_constant_else_constant() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_if_constant_then_constant_else_public() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Constant, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_if_constant_then_constant_else_private() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Constant, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_if_constant_then_public_else_constant() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_if_constant_then_public_else_public() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Public, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_if_constant_then_public_else_private() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Public, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_if_constant_then_private_else_constant() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_if_constant_then_private_else_public() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Private, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_if_constant_then_private_else_private() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Private, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_if_public_then_constant_else_constant() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_if_public_then_constant_else_public() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Constant, Mode::Public, 0, 0, 64, 64);
    }

    #[test]
    fn test_u64_if_public_then_constant_else_private() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Constant, Mode::Private, 0, 0, 64, 64);
    }

    #[test]
    fn test_u64_if_public_then_public_else_constant() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Public, Mode::Constant, 0, 0, 64, 64);
    }

    #[test]
    fn test_u64_if_public_then_public_else_public() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Public, Mode::Public, 0, 0, 64, 64);
    }

    #[test]
    fn test_u64_if_public_then_public_else_private() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Public, Mode::Private, 0, 0, 64, 64);
    }

    #[test]
    fn test_u64_if_public_then_private_else_constant() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Private, Mode::Constant, 0, 0, 64, 64);
    }

    #[test]
    fn test_u64_if_public_then_private_else_public() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Private, Mode::Public, 0, 0, 64, 64);
    }

    #[test]
    fn test_u64_if_public_then_private_else_private() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Private, Mode::Private, 0, 0, 64, 64);
    }

    #[test]
    fn test_u64_if_private_then_constant_else_constant() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_if_private_then_constant_else_public() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Constant, Mode::Public, 0, 0, 64, 64);
    }

    #[test]
    fn test_u64_if_private_then_constant_else_private() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Constant, Mode::Private, 0, 0, 64, 64);
    }

    #[test]
    fn test_u64_if_private_then_public_else_constant() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Public, Mode::Constant, 0, 0, 64, 64);
    }

    #[test]
    fn test_u64_if_private_then_public_else_public() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Public, Mode::Public, 0, 0, 64, 64);
    }

    #[test]
    fn test_u64_if_private_then_public_else_private() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Public, Mode::Private, 0, 0, 64, 64);
    }

    #[test]
    fn test_u64_if_private_then_private_else_constant() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Private, Mode::Constant, 0, 0, 64, 64);
    }

    #[test]
    fn test_u64_if_private_then_private_else_public() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Private, Mode::Public, 0, 0, 64, 64);
    }

    #[test]
    fn test_u64_if_private_then_private_else_private() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Private, Mode::Private, 0, 0, 64, 64);
    }

    // Tests for i64.

    #[test]
    fn test_i64_if_constant_then_constant_else_constant() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_if_constant_then_constant_else_public() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Constant, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_if_constant_then_constant_else_private() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Constant, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_if_constant_then_public_else_constant() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_if_constant_then_public_else_public() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Public, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_if_constant_then_public_else_private() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Public, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_if_constant_then_private_else_constant() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_if_constant_then_private_else_public() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Private, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_if_constant_then_private_else_private() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Private, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_if_public_then_constant_else_constant() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_if_public_then_constant_else_public() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Constant, Mode::Public, 0, 0, 64, 64);
    }

    #[test]
    fn test_i64_if_public_then_constant_else_private() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Constant, Mode::Private, 0, 0, 64, 64);
    }

    #[test]
    fn test_i64_if_public_then_public_else_constant() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Public, Mode::Constant, 0, 0, 64, 64);
    }

    #[test]
    fn test_i64_if_public_then_public_else_public() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Public, Mode::Public, 0, 0, 64, 64);
    }

    #[test]
    fn test_i64_if_public_then_public_else_private() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Public, Mode::Private, 0, 0, 64, 64);
    }

    #[test]
    fn test_i64_if_public_then_private_else_constant() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Private, Mode::Constant, 0, 0, 64, 64);
    }

    #[test]
    fn test_i64_if_public_then_private_else_public() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Private, Mode::Public, 0, 0, 64, 64);
    }

    #[test]
    fn test_i64_if_public_then_private_else_private() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Private, Mode::Private, 0, 0, 64, 64);
    }

    #[test]
    fn test_i64_if_private_then_constant_else_constant() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_if_private_then_constant_else_public() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Constant, Mode::Public, 0, 0, 64, 64);
    }

    #[test]
    fn test_i64_if_private_then_constant_else_private() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Constant, Mode::Private, 0, 0, 64, 64);
    }

    #[test]
    fn test_i64_if_private_then_public_else_constant() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Public, Mode::Constant, 0, 0, 64, 64);
    }

    #[test]
    fn test_i64_if_private_then_public_else_public() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Public, Mode::Public, 0, 0, 64, 64);
    }

    #[test]
    fn test_i64_if_private_then_public_else_private() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Public, Mode::Private, 0, 0, 64, 64);
    }

    #[test]
    fn test_i64_if_private_then_private_else_constant() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Private, Mode::Constant, 0, 0, 64, 64);
    }

    #[test]
    fn test_i64_if_private_then_private_else_public() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Private, Mode::Public, 0, 0, 64, 64);
    }

    #[test]
    fn test_i64_if_private_then_private_else_private() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Private, Mode::Private, 0, 0, 64, 64);
    }

    // Tests for u128.

    #[test]
    fn test_u128_if_constant_then_constant_else_constant() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_if_constant_then_constant_else_public() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Constant, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_if_constant_then_constant_else_private() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Constant, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_if_constant_then_public_else_constant() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_if_constant_then_public_else_public() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Public, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_if_constant_then_public_else_private() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Public, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_if_constant_then_private_else_constant() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_if_constant_then_private_else_public() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Private, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_if_constant_then_private_else_private() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Private, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_if_public_then_constant_else_constant() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_if_public_then_constant_else_public() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Constant, Mode::Public, 0, 0, 128, 128);
    }

    #[test]
    fn test_u128_if_public_then_constant_else_private() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Constant, Mode::Private, 0, 0, 128, 128);
    }

    #[test]
    fn test_u128_if_public_then_public_else_constant() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Public, Mode::Constant, 0, 0, 128, 128);
    }

    #[test]
    fn test_u128_if_public_then_public_else_public() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Public, Mode::Public, 0, 0, 128, 128);
    }

    #[test]
    fn test_u128_if_public_then_public_else_private() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Public, Mode::Private, 0, 0, 128, 128);
    }

    #[test]
    fn test_u128_if_public_then_private_else_constant() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Private, Mode::Constant, 0, 0, 128, 128);
    }

    #[test]
    fn test_u128_if_public_then_private_else_public() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Private, Mode::Public, 0, 0, 128, 128);
    }

    #[test]
    fn test_u128_if_public_then_private_else_private() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Private, Mode::Private, 0, 0, 128, 128);
    }

    #[test]
    fn test_u128_if_private_then_constant_else_constant() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_if_private_then_constant_else_public() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Constant, Mode::Public, 0, 0, 128, 128);
    }

    #[test]
    fn test_u128_if_private_then_constant_else_private() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Constant, Mode::Private, 0, 0, 128, 128);
    }

    #[test]
    fn test_u128_if_private_then_public_else_constant() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Public, Mode::Constant, 0, 0, 128, 128);
    }

    #[test]
    fn test_u128_if_private_then_public_else_public() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Public, Mode::Public, 0, 0, 128, 128);
    }

    #[test]
    fn test_u128_if_private_then_public_else_private() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Public, Mode::Private, 0, 0, 128, 128);
    }

    #[test]
    fn test_u128_if_private_then_private_else_constant() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Private, Mode::Constant, 0, 0, 128, 128);
    }

    #[test]
    fn test_u128_if_private_then_private_else_public() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Private, Mode::Public, 0, 0, 128, 128);
    }

    #[test]
    fn test_u128_if_private_then_private_else_private() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Private, Mode::Private, 0, 0, 128, 128);
    }

    // Tests for i128.

    #[test]
    fn test_i128_if_constant_then_constant_else_constant() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_if_constant_then_constant_else_public() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Constant, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_if_constant_then_constant_else_private() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Constant, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_if_constant_then_public_else_constant() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_if_constant_then_public_else_public() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Public, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_if_constant_then_public_else_private() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Public, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_if_constant_then_private_else_constant() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_if_constant_then_private_else_public() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Private, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_if_constant_then_private_else_private() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Private, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_if_public_then_constant_else_constant() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_if_public_then_constant_else_public() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Constant, Mode::Public, 0, 0, 128, 128);
    }

    #[test]
    fn test_i128_if_public_then_constant_else_private() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Constant, Mode::Private, 0, 0, 128, 128);
    }

    #[test]
    fn test_i128_if_public_then_public_else_constant() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Public, Mode::Constant, 0, 0, 128, 128);
    }

    #[test]
    fn test_i128_if_public_then_public_else_public() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Public, Mode::Public, 0, 0, 128, 128);
    }

    #[test]
    fn test_i128_if_public_then_public_else_private() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Public, Mode::Private, 0, 0, 128, 128);
    }

    #[test]
    fn test_i128_if_public_then_private_else_constant() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Private, Mode::Constant, 0, 0, 128, 128);
    }

    #[test]
    fn test_i128_if_public_then_private_else_public() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Private, Mode::Public, 0, 0, 128, 128);
    }

    #[test]
    fn test_i128_if_public_then_private_else_private() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Private, Mode::Private, 0, 0, 128, 128);
    }

    #[test]
    fn test_i128_if_private_then_constant_else_constant() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_if_private_then_constant_else_public() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Constant, Mode::Public, 0, 0, 128, 128);
    }

    #[test]
    fn test_i128_if_private_then_constant_else_private() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Constant, Mode::Private, 0, 0, 128, 128);
    }

    #[test]
    fn test_i128_if_private_then_public_else_constant() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Public, Mode::Constant, 0, 0, 128, 128);
    }

    #[test]
    fn test_i128_if_private_then_public_else_public() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Public, Mode::Public, 0, 0, 128, 128);
    }

    #[test]
    fn test_i128_if_private_then_public_else_private() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Public, Mode::Private, 0, 0, 128, 128);
    }

    #[test]
    fn test_i128_if_private_then_private_else_constant() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Private, Mode::Constant, 0, 0, 128, 128);
    }

    #[test]
    fn test_i128_if_private_then_private_else_public() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Private, Mode::Public, 0, 0, 128, 128);
    }

    #[test]
    fn test_i128_if_private_then_private_else_private() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Private, Mode::Private, 0, 0, 128, 128);
    }
}
