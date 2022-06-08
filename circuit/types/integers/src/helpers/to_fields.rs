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

impl<E: Environment, I: IntegerType> ToFields for Integer<E, I> {
    type Field = Field<E>;

    /// Casts an integer into a list of base fields.
    fn to_fields(&self) -> Vec<Self::Field> {
        vec![self.to_field()]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    const ITERATIONS: u64 = 128;

    fn check_to_fields<I: IntegerType>(mode: Mode) {
        for i in 0..ITERATIONS {
            // Sample a random integer.
            let expected = Uniform::rand(&mut test_rng());
            let candidate = Integer::<Circuit, I>::new(mode, expected);

            Circuit::scope(format!("{mode} {expected} {i}"), || {
                // Perform the operation.
                let candidate = candidate.to_fields();
                assert_eq!(1, candidate.len());
                assert_scope!(0, 0, 0, 0);

                // Extract the bits from the base field representation.
                let candidate_bits_le = candidate[0].eject_value().to_bits_le();
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
    fn test_u8_to_fields() {
        type I = u8;
        check_to_fields::<I>(Mode::Constant);
        check_to_fields::<I>(Mode::Public);
        check_to_fields::<I>(Mode::Private);
    }

    #[test]
    fn test_i8_to_fields() {
        type I = i8;
        check_to_fields::<I>(Mode::Constant);
        check_to_fields::<I>(Mode::Public);
        check_to_fields::<I>(Mode::Private);
    }

    #[test]
    fn test_u16_to_fields() {
        type I = u16;
        check_to_fields::<I>(Mode::Constant);
        check_to_fields::<I>(Mode::Public);
        check_to_fields::<I>(Mode::Private);
    }

    #[test]
    fn test_i16_to_fields() {
        type I = i16;
        check_to_fields::<I>(Mode::Constant);
        check_to_fields::<I>(Mode::Public);
        check_to_fields::<I>(Mode::Private);
    }

    #[test]
    fn test_u32_to_fields() {
        type I = u32;
        check_to_fields::<I>(Mode::Constant);
        check_to_fields::<I>(Mode::Public);
        check_to_fields::<I>(Mode::Private);
    }

    #[test]
    fn test_i32_to_fields() {
        type I = i32;
        check_to_fields::<I>(Mode::Constant);
        check_to_fields::<I>(Mode::Public);
        check_to_fields::<I>(Mode::Private);
    }

    #[test]
    fn test_u64_to_fields() {
        type I = u64;
        check_to_fields::<I>(Mode::Constant);
        check_to_fields::<I>(Mode::Public);
        check_to_fields::<I>(Mode::Private);
    }

    #[test]
    fn test_i64_to_fields() {
        type I = i64;
        check_to_fields::<I>(Mode::Constant);
        check_to_fields::<I>(Mode::Public);
        check_to_fields::<I>(Mode::Private);
    }

    #[test]
    fn test_u128_to_fields() {
        type I = u128;
        check_to_fields::<I>(Mode::Constant);
        check_to_fields::<I>(Mode::Public);
        check_to_fields::<I>(Mode::Private);
    }

    #[test]
    fn test_i128_to_fields() {
        type I = i128;
        check_to_fields::<I>(Mode::Constant);
        check_to_fields::<I>(Mode::Public);
        check_to_fields::<I>(Mode::Private);
    }
}
