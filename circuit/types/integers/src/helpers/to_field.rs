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

impl<E: Environment, I: IntegerType> ToField for Integer<E, I> {
    type Field = Field<E>;

    /// Casts an integer into a base field.
    fn to_field(&self) -> Self::Field {
        // Note: We are reconstituting the integer as a base field.
        // This is safe as the number of bits in the integer is less than the base field modulus,
        // and thus will always fit within a single base field element.
        debug_assert!(I::BITS < E::BaseField::size_in_bits() as u64);

        // Reconstruct the bits as a linear combination representing the original field value.
        Field::from_bits_le(&self.bits_le)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    const ITERATIONS: u64 = 128;

    fn check_to_field<I: IntegerType>(mode: Mode) {
        for i in 0..ITERATIONS {
            // Sample a random integer.
            let expected = Uniform::rand(&mut test_rng());
            let candidate = Integer::<Circuit, I>::new(mode, expected);

            Circuit::scope(format!("{mode} {expected} {i}"), || {
                // Perform the operation.
                let candidate = candidate.to_field();
                assert_scope!(0, 0, 0, 0);

                // Extract the bits from the base field representation.
                let candidate_bits_le = candidate.eject_value().to_bits_le();
                assert_eq!(<Circuit as Environment>::BaseField::size_in_bits(), candidate_bits_le.len());

                // Ensure all integer bits match with the expected result.
                let expected_bits = expected.to_bits_le();
                for (expected_bit, candidate_bit) in
                    expected_bits.iter().zip_eq(&candidate_bits_le[0..I::BITS as usize])
                {
                    assert_eq!(expected_bit, candidate_bit);
                }

                // Ensure all remaining bits are 0.
                for candidate_bit in &candidate_bits_le[I::BITS as usize..] {
                    assert!(!candidate_bit);
                }
            });
            Circuit::reset();
        }
    }

    #[test]
    fn test_u8_to_field() {
        type I = u8;
        check_to_field::<I>(Mode::Constant);
        check_to_field::<I>(Mode::Public);
        check_to_field::<I>(Mode::Private);
    }

    #[test]
    fn test_i8_to_field() {
        type I = i8;
        check_to_field::<I>(Mode::Constant);
        check_to_field::<I>(Mode::Public);
        check_to_field::<I>(Mode::Private);
    }

    #[test]
    fn test_u16_to_field() {
        type I = u16;
        check_to_field::<I>(Mode::Constant);
        check_to_field::<I>(Mode::Public);
        check_to_field::<I>(Mode::Private);
    }

    #[test]
    fn test_i16_to_field() {
        type I = i16;
        check_to_field::<I>(Mode::Constant);
        check_to_field::<I>(Mode::Public);
        check_to_field::<I>(Mode::Private);
    }

    #[test]
    fn test_u32_to_field() {
        type I = u32;
        check_to_field::<I>(Mode::Constant);
        check_to_field::<I>(Mode::Public);
        check_to_field::<I>(Mode::Private);
    }

    #[test]
    fn test_i32_to_field() {
        type I = i32;
        check_to_field::<I>(Mode::Constant);
        check_to_field::<I>(Mode::Public);
        check_to_field::<I>(Mode::Private);
    }

    #[test]
    fn test_u64_to_field() {
        type I = u64;
        check_to_field::<I>(Mode::Constant);
        check_to_field::<I>(Mode::Public);
        check_to_field::<I>(Mode::Private);
    }

    #[test]
    fn test_i64_to_field() {
        type I = i64;
        check_to_field::<I>(Mode::Constant);
        check_to_field::<I>(Mode::Public);
        check_to_field::<I>(Mode::Private);
    }

    #[test]
    fn test_u128_to_field() {
        type I = u128;
        check_to_field::<I>(Mode::Constant);
        check_to_field::<I>(Mode::Public);
        check_to_field::<I>(Mode::Private);
    }

    #[test]
    fn test_i128_to_field() {
        type I = i128;
        check_to_field::<I>(Mode::Constant);
        check_to_field::<I>(Mode::Public);
        check_to_field::<I>(Mode::Private);
    }
}
