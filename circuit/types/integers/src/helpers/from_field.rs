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

impl<E: Environment, I: IntegerType> FromField for Integer<E, I> {
    type Field = Field<E>;

    /// Casts an integer from a base field.
    fn from_field(field: Self::Field) -> Self {
        // Note: We are reconstituting the integer from the base field.
        // This is safe as the number of bits in the integer is less than the base field modulus,
        // and thus will always fit within a single base field element.
        debug_assert!(I::BITS < E::BaseField::size_in_bits() as u64);

        // Extract the integer bits from the field element, **without** a carry bit.
        let bits_le = field.to_lower_bits_le(I::BITS as usize);

        // Return the integer.
        Integer { bits_le, phantom: Default::default() }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    const ITERATIONS: u64 = 128;

    fn check_from_field<I: IntegerType>(mode: Mode) {
        for i in 0..ITERATIONS {
            // Sample a random integer.
            let expected = Uniform::rand(&mut test_rng());
            let candidate = Integer::<Circuit, I>::new(mode, expected).to_field();

            Circuit::scope(format!("{mode} {expected} {i}"), || {
                // Perform the operation.
                let candidate = Integer::from_field(candidate);
                assert_eq!(expected, candidate.eject_value());
                match mode {
                    Mode::Constant => assert_scope!(I::BITS, 0, 0, 0),
                    _ => assert_scope!(0, 0, I::BITS, I::BITS + 1),
                }
            });
            Circuit::reset();
        }
    }

    #[test]
    fn test_u8_from_field() {
        type I = u8;
        check_from_field::<I>(Mode::Constant);
        check_from_field::<I>(Mode::Public);
        check_from_field::<I>(Mode::Private);
    }

    #[test]
    fn test_i8_from_field() {
        type I = i8;
        check_from_field::<I>(Mode::Constant);
        check_from_field::<I>(Mode::Public);
        check_from_field::<I>(Mode::Private);
    }

    #[test]
    fn test_u16_from_field() {
        type I = u16;
        check_from_field::<I>(Mode::Constant);
        check_from_field::<I>(Mode::Public);
        check_from_field::<I>(Mode::Private);
    }

    #[test]
    fn test_i16_from_field() {
        type I = i16;
        check_from_field::<I>(Mode::Constant);
        check_from_field::<I>(Mode::Public);
        check_from_field::<I>(Mode::Private);
    }

    #[test]
    fn test_u32_from_field() {
        type I = u32;
        check_from_field::<I>(Mode::Constant);
        check_from_field::<I>(Mode::Public);
        check_from_field::<I>(Mode::Private);
    }

    #[test]
    fn test_i32_from_field() {
        type I = i32;
        check_from_field::<I>(Mode::Constant);
        check_from_field::<I>(Mode::Public);
        check_from_field::<I>(Mode::Private);
    }

    #[test]
    fn test_u64_from_field() {
        type I = u64;
        check_from_field::<I>(Mode::Constant);
        check_from_field::<I>(Mode::Public);
        check_from_field::<I>(Mode::Private);
    }

    #[test]
    fn test_i64_from_field() {
        type I = i64;
        check_from_field::<I>(Mode::Constant);
        check_from_field::<I>(Mode::Public);
        check_from_field::<I>(Mode::Private);
    }

    #[test]
    fn test_u128_from_field() {
        type I = u128;
        check_from_field::<I>(Mode::Constant);
        check_from_field::<I>(Mode::Public);
        check_from_field::<I>(Mode::Private);
    }

    #[test]
    fn test_i128_from_field() {
        type I = i128;
        check_from_field::<I>(Mode::Constant);
        check_from_field::<I>(Mode::Public);
        check_from_field::<I>(Mode::Private);
    }
}
