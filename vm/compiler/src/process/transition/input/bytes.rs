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

impl<N: Network> FromBytes for Input<N> {
    /// Reads the input from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let index = u16::read_le(&mut reader)?;
        let literal = match index {
            0 => {
                let plaintext_hash: Field<N> = FromBytes::read_le(&mut reader)?;
                let plaintext_exists: bool = FromBytes::read_le(&mut reader)?;
                let plaintext = match plaintext_exists {
                    true => Some(FromBytes::read_le(&mut reader)?),
                    false => None,
                };

                Self::Constant(plaintext_hash, plaintext)
            }
            1 => {
                let plaintext_hash: Field<N> = FromBytes::read_le(&mut reader)?;
                let plaintext_exists: bool = FromBytes::read_le(&mut reader)?;
                let plaintext = match plaintext_exists {
                    true => Some(FromBytes::read_le(&mut reader)?),
                    false => None,
                };
                Self::Public(plaintext_hash, plaintext)
            }
            2 => {
                let ciphertext_hash: Field<N> = FromBytes::read_le(&mut reader)?;
                let ciphertext_exists: bool = FromBytes::read_le(&mut reader)?;
                let ciphertext = match ciphertext_exists {
                    true => Some(FromBytes::read_le(&mut reader)?),
                    false => None,
                };
                Self::Private(ciphertext_hash, ciphertext)
            }
            3 => Self::Record(FromBytes::read_le(&mut reader)?),
            4 => Self::ExternalRecord(FromBytes::read_le(&mut reader)?),
            5.. => return Err(error(format!("Failed to decode input variant {index}"))),
        };
        Ok(literal)
    }
}

impl<N: Network> ToBytes for Input<N> {
    /// Writes the input to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        type Size = u16;
        match self {
            Self::Constant(plaintext_hash, plaintext) => {
                (0 as Size).write_le(&mut writer)?;
                plaintext_hash.write_le(&mut writer)?;
                match plaintext {
                    Some(plaintext) => {
                        true.write_le(&mut writer)?;
                        plaintext.write_le(&mut writer)
                    }
                    None => false.write_le(&mut writer),
                }
            }
            Self::Public(plaintext_hash, plaintext) => {
                (1 as Size).write_le(&mut writer)?;
                plaintext_hash.write_le(&mut writer)?;
                match plaintext {
                    Some(plaintext) => {
                        true.write_le(&mut writer)?;
                        plaintext.write_le(&mut writer)
                    }
                    None => false.write_le(&mut writer),
                }
            }
            Self::Private(ciphertext_hash, ciphertext) => {
                (2 as Size).write_le(&mut writer)?;
                ciphertext_hash.write_le(&mut writer)?;
                match ciphertext {
                    Some(ciphertext) => {
                        true.write_le(&mut writer)?;
                        ciphertext.write_le(&mut writer)
                    }
                    None => false.write_le(&mut writer),
                }
            }
            Self::Record(serial_number) => {
                (3 as Size).write_le(&mut writer)?;
                serial_number.write_le(&mut writer)
            }
            Self::ExternalRecord(input_commitment) => {
                (4 as Size).write_le(&mut writer)?;
                input_commitment.write_le(&mut writer)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: u32 = 1000;

    fn check_bytes(expected: Input<CurrentNetwork>) -> Result<()> {
        // Check the byte representation.
        let expected_bytes = expected.to_bytes_le()?;
        assert_eq!(expected, Input::read_le(&expected_bytes[..])?);
        Ok(())
    }

    #[test]
    fn test_bytes() -> Result<()> {
        let rng = &mut test_rng();

        for _ in 0..ITERATIONS {
            let plaintext = Plaintext::<CurrentNetwork>::from_str("true")?;
            let ciphertext =
                Ciphertext::<CurrentNetwork>::try_from((0..100).map(|_| Uniform::rand(rng)).collect::<Vec<_>>())
                    .unwrap();

            // Constant
            check_bytes(Input::<CurrentNetwork>::Constant(Uniform::rand(rng), Some(plaintext.clone())))?;
            check_bytes(Input::<CurrentNetwork>::Constant(Uniform::rand(rng), None))?;

            // Public
            check_bytes(Input::<CurrentNetwork>::Public(Uniform::rand(rng), Some(plaintext.clone())))?;
            check_bytes(Input::<CurrentNetwork>::Public(Uniform::rand(rng), None))?;

            // Private
            check_bytes(Input::<CurrentNetwork>::Private(Uniform::rand(rng), Some(ciphertext)))?;
            check_bytes(Input::<CurrentNetwork>::Private(Uniform::rand(rng), None))?;

            // Record
            check_bytes(Input::<CurrentNetwork>::Record(Uniform::rand(rng)))?;

            // ExternalRecord
            check_bytes(Input::<CurrentNetwork>::ExternalRecord(Uniform::rand(rng)))?;
        }
        Ok(())
    }
}
