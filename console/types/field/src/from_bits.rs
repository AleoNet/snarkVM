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

impl<E: Environment> FromBits for Field<E> {
    /// Initializes a new field from a list of **little-endian** bits.
    ///   - If `bits_le` is longer than `E::Field::size_in_bits()`, the excess bits are enforced to be `0`s.
    ///   - If `bits_le` is shorter than `E::Field::size_in_bits()`, it is padded with `0`s up to field size.
    fn from_bits_le(bits_le: &[bool]) -> Result<Self> {
        // Retrieve the data and field size.
        let size_in_data_bits = Field::<E>::size_in_data_bits();
        let size_in_bits = Field::<E>::size_in_bits();

        // Ensure the list of booleans is within the allowed size in bits.
        let num_bits = bits_le.len();
        if num_bits > size_in_bits {
            // Check if all excess bits are zero.
            let should_be_zero = bits_le[size_in_bits..].iter().fold(false, |acc, bit| acc | bit);
            // Ensure `should_be_zero` is `false`.
            ensure!(!should_be_zero, "The excess bits are not zero.");
        }

        // If `num_bits` is greater than `size_in_data_bits`, check it is less than `Field::MODULUS`.
        if num_bits > size_in_data_bits {
            // Recover the field as a `BigInteger` for comparison.
            // As `bits_le[size_in_bits..]` is guaranteed to be zero from the above logic,
            // and `bits_le` is greater than `size_in_data_bits`, it is safe to truncate `bits_le` to `size_in_bits`.
            let field = E::BigInteger::from_bits_le(&bits_le[..size_in_bits])?;

            // Ensure the field is less than `Field::MODULUS`.
            ensure!(field < E::Field::modulus(), "The field is greater than or equal to the modulus.");

            // Return the field.
            Ok(Field { field: E::Field::from_repr(field).ok_or_else(|| anyhow!("Invalid field from bits"))? })
        } else {
            // Construct the sanitized list of bits, resizing up if necessary.
            let mut bits_le = bits_le.iter().take(size_in_bits).cloned().collect::<Vec<_>>();
            bits_le.resize(size_in_bits, false);

            // Recover the native field.
            let field = E::Field::from_repr(E::BigInteger::from_bits_le(&bits_le)?)
                .ok_or_else(|| anyhow!("Invalid field from bits"))?;

            // Return the field.
            Ok(Field { field })
        }
    }

    /// Initializes a new field from a list of big-endian bits *without* leading zeros.
    fn from_bits_be(bits_be: &[bool]) -> Result<Self> {
        // Reverse the given bits from big-endian into little-endian.
        // Note: This is safe as the bit representation is consistent (there are no leading zeros).
        let mut bits_le = bits_be.to_vec();
        bits_le.reverse();

        Self::from_bits_le(&bits_le)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network_environment::Console;

    type CurrentEnvironment = Console;

    const ITERATIONS: u64 = 100;

    fn check_from_bits_le() -> Result<()> {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected: Field<CurrentEnvironment> = Uniform::rand(&mut test_rng());
            let given_bits = expected.to_bits_le();
            assert_eq!(Field::<CurrentEnvironment>::size_in_bits(), given_bits.len());

            let candidate = Field::<CurrentEnvironment>::from_bits_le(&given_bits)?;
            assert_eq!(expected, candidate);

            // Add excess zero bits.
            let candidate = vec![given_bits, vec![false; i as usize]].concat();

            let candidate = Field::<CurrentEnvironment>::from_bits_le(&candidate)?;
            assert_eq!(expected, candidate);
            assert_eq!(Field::<CurrentEnvironment>::size_in_bits(), candidate.to_bits_le().len());
        }
        Ok(())
    }

    fn check_from_bits_be() -> Result<()> {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected: Field<CurrentEnvironment> = Uniform::rand(&mut test_rng());
            let given_bits = expected.to_bits_be();
            assert_eq!(Field::<CurrentEnvironment>::size_in_bits(), given_bits.len());

            let candidate = Field::<CurrentEnvironment>::from_bits_be(&given_bits)?;
            assert_eq!(expected, candidate);

            // Add excess zero bits.
            let candidate = vec![vec![false; i as usize], given_bits].concat();

            let candidate = Field::<CurrentEnvironment>::from_bits_be(&candidate)?;
            assert_eq!(expected, candidate);
            assert_eq!(Field::<CurrentEnvironment>::size_in_bits(), candidate.to_bits_be().len());
        }
        Ok(())
    }

    #[test]
    fn test_from_bits_le() -> Result<()> {
        check_from_bits_le()
    }

    #[test]
    fn test_from_bits_be() -> Result<()> {
        check_from_bits_be()
    }
}
